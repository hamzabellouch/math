import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction Laplacian ContDiff
namespace FrozenParametrix
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma c0Time_eq_sourceValue (hα : 0 < α) (a : V →ᵇ Icc α β)
    (q : ℝ) (hq : 0 < q) (f : C₀(V,ℂ)) (x : V) :
    c0Time hα a q f x = SourceFrozenRows.value (heatKernel 1 zero_lt_one)
      (fun y => (a y).val) (q^(1/4 : ℝ)) f.toBCF x := by
  rw [c0Time_apply hα a q hq f, timeValue_eq_scaled hα a.toContinuousMap q hq f]
  unfold SourceFrozenRows.value
  have he : sourceScale a.toContinuousMap q = fun y => q^(1/4 : ℝ)*(a y).val^(1/4 : ℝ) := by
    funext y
    unfold sourceScale
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
    change ((q*(a y).val)^(1/2 : ℝ))^(1/2 : ℝ) = _
    rw [← Real.rpow_mul (mul_nonneg hq.le (hα.trans_le (a y).property.1).le)]
    norm_num
    exact Real.mul_rpow hq.le (hα.trans_le (a y).property.1).le
  rw [he]
  rfl
end FrozenParametrix

namespace ParametrixVolterra
section ExtendedA
open FrozenParametrix StrongWeightedVolterra BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V]
variable {T α β : ℝ}
variable (A : C(Slab T,V →ᵇ Icc α β)) (hT : 0 ≤ T)

def extendedA (s : ℝ) (x : V) : ℝ := (A (projIcc 0 T hT s) x).val

lemma continuous_extendedA : Continuous (Function.uncurry (extendedA A hT)) := by
  change Continuous (fun p : ℝ × V => (A (projIcc 0 T hT p.1) p.2).val)
  have h : Continuous (fun p : ℝ × V => A (projIcc 0 T hT p.1) p.2) := by fun_prop
  exact continuous_subtype_val.comp h

lemma extendedA_range (s : ℝ) (x : V) : extendedA A hT s x ∈ Icc α β :=
  (A (projIcc 0 T hT s) x).property

lemma extendedA_lipschitz (L : ℝ)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∀ s x y, ‖extendedA A hT s x-extendedA A hT s y‖ ≤ L*‖x-y‖ := by
  intro s x y
  simpa only [extendedA,Real.norm_eq_abs,sub_self,abs_zero,add_zero] using
    hLip (projIcc 0 T hT s) (projIcc 0 T hT s) x y

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (hα : 0 < α)
lemma duhamel_eq_sourceDuhamel (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) (x : V) :
    duhamel hα A j t.val x = SourceFrozenRows.duhamel (heatKernel 1 zero_lt_one)
      (extendedA A hT) (fun s => (unweighted j s).toBCF) t.val x := by
  unfold duhamel SourceFrozenRows.duhamel
  rw [HolderIntegral.intervalIntegral_apply _ (intervalIntegrable_sourceFrozen hα A j t.val t.val
    ⟨t.property.1.le,t.property.2⟩) x,
    intervalIntegral.integral_of_le t.property.1.le,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hsT : s ∈ Ioc (0:ℝ) T := ⟨hs.1,hs.2.le.trans t.property.2⟩
  dsimp only
  rw [VolterraIntegral.sourceExtend_apply _ _ _ hsT]
  dsimp [sourceFrozen]
  rw [c0Time_eq_sourceValue hα _ _ (sub_pos.mpr hs.2)]
  have he : projIcc 0 T hT s = now (⟨s,hsT⟩ : Time T) :=
    projIcc_of_mem hT ⟨hs.1.le,hsT.2⟩
  have heA : extendedA A hT s = fun y => (A (now (⟨s,hsT⟩ : Time T)) y).val := by
    funext y
    unfold extendedA
    rw [he]
  rw [heA]

include hT in
lemma contDiff_duhamel_of_holder (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hj : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
    (t : Time T) : ContDiff ℝ 4 (fun x => duhamel hα A j t.val x) := by
  have hf : StronglyMeasurable (fun s => (unweighted j s).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_unweighted j)
  have hn : ∀ s ∈ Ioo 0 t.val, ‖(unweighted j s).toBCF‖ ≤ ‖j‖*s^(-(3/4 : ℝ)) := by
    intro s hs
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    simpa only [neg_div,mul_comm] using norm_unweighted_le j s hs.1
  have hh : ∀ s ∈ Ioo 0 t.val, ∀ x y : V,
      ‖(unweighted j s).toBCF x-(unweighted j s).toBCF y‖ ≤
        (H*s^(-(7/8 : ℝ)))*‖x-y‖^(1/4 : ℝ) := by
    intro s hs x y
    change ‖unweighted j s x-unweighted j s y‖ ≤ _
    simpa only [neg_div] using hj ⟨s,hs.1,hs.2.le.trans t.property.2⟩ x y
  have he := funext (duhamel_eq_sourceDuhamel A hT hα j t)
  rw [he]
  exact WeightedSourceFrozenRows.contDiff_duhamel (heatKernel 1 zero_lt_one) (extendedA A hT)
    (continuous_extendedA A hT) α β hα (extendedA_range A hT) L hL (extendedA_lipschitz A hT L hLip)
    (fun s => (unweighted j s).toBCF) hf (3/4) (7/8) ‖j‖ H (1/4) t.val
    (by norm_num) (by norm_num) (norm_nonneg j) hH t.property.1 (by norm_num) (by norm_num) hn hh
end ExtendedA

open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β))
    (b : C(Slab T,V →ᵇ ℂ))

lemma contDiff_mildTime_of_correction (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ))
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = -actualResidual hα A b t (initial hT₀) d)
    (t : Time T) : ContDiff ℝ 4 (fun x => mildTime hα A hT₀ d j t.val x) := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_holder_bound hα A b hT L B hL hB hb hLip hLipb
    (1/4) (by norm_num) (by norm_num)
  have hR' : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := by
    convert hR using 1; norm_num
  obtain ⟨H,hH,hholder⟩ := correction_holder hα A b hT₀ hT C hC hR' d 0 j 0 le_rfl
    (by intro t x y; simp) hi (by simpa using hj)
  have h0 : ContDiff ℝ 4 (fun x => c0Time hα (A (initial hT₀)) t.val d x) := by
    have he := funext (c0Time_apply hα (A (initial hT₀)) t.val t.property.1 d)
    rw [he]
    exact contDiff_infty.mp (contDiff_timeValue hα (A (initial hT₀)).toContinuousMap t.val t.property.1 d) 4
  exact h0.add (contDiff_duhamel_of_holder A hT₀ hα L hL hLip j H hH hholder t)
end ParametrixVolterra

end

end OAI
