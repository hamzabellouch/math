import OAI.Analysis.AncientFlat.Evolution.ClassicalSpatial

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap ContDiff
namespace ParametrixVolterra
section HolderResidualIntegralGamma
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
variable {γ : ℝ}
lemma holder_residual_integral_gamma (hT₀ : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^γ)
    (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T)
    (hi : IntervalIntegrable (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (x y : V) :
    ‖(∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) x-
      (∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) y‖ ≤
      (C*‖j‖)*t.val^(-5/8 : ℝ)*(∫ s in 0..1, BetaWeights.density (3/4) (7/8) 1 s)*‖x-y‖^γ := by
  have hh := HolderIntegral.beta_holder (x := x) (y := y)
    (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) t.val t.property.1 hi
    (3/4) (7/8) (by norm_num) (by norm_num) (C*‖j‖) (‖x-y‖^γ)
  apply (show 1-(3/4 : ℝ)-7/8 = -5/8 by norm_num) ▸ hh
  intro r hr
  let s : Slab T := ⟨r,hr.1.le,hr.2.le.trans t.property.2⟩
  have he : projIcc 0 T hT₀ r = s := projIcc_of_mem hT₀ s.property
  have hu : ‖unweighted j r‖ ≤ r^(-3/4 : ℝ)*‖j‖ := by
    let u : Time T := ⟨r,hr.1,hr.2.le.trans t.property.2⟩
    change ‖unweighted j u.val‖ ≤ _
    rw [unweighted_at_time,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    exact mul_le_mul_of_nonneg_left (j.norm_coe_le_norm u) (Real.rpow_nonneg hr.1.le _)
  simp only [residualKernel,ite_eq_left hr,he]
  calc
    _ ≤ C*‖unweighted j r‖*(t.val-r)^(-7/8 : ℝ)*‖x-y‖^γ := hR t s hr.2 _ x y
    _ ≤ C*(r^(-3/4 : ℝ)*‖j‖)*(t.val-r)^(-7/8 : ℝ)*‖x-y‖^γ := by
      gcongr
      exact Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _
    _ = _ := by unfold BetaWeights.density; ring_nf

lemma correction_holder_gamma (hT₀ : 0 ≤ T) (hT : T ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^γ)
    (d : C₀(V,ℂ)) (l j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^γ)
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = l t-actualResidual hα A b t (initial hT₀) d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Time T, ∀ x y,
      ‖unweighted j t.val x-unweighted j t.val y‖ ≤ D*t.val^(-7/8 : ℝ)*‖x-y‖^γ := by
  let Q := ∫ s in 0..1, BetaWeights.density (3/4) (7/8) 1 s
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (fun s hs => BetaWeights.density_nonneg _ _ _ _ hs.1 hs.2)
  refine ⟨H+C*‖d‖+C*‖j‖*Q,by positivity,fun t x y => ?_⟩
  let v := ∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)
  have he : unweighted j t.val = l t-actualResidual hα A b t (initial hT₀) d-v :=
    eq_sub_of_add_eq (hj t)
  have hd := hR t (initial hT₀) t.property.1 d x y
  simp only [initial,sub_zero] at hd
  have hv := holder_residual_integral_gamma hα A b hT₀ C hC hR j t (hi t) x y
  have ht1 : t.val ≤ 1 := t.property.2.trans hT
  have hp : 1 ≤ t.val^(-7/8 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos t.property.1 ht1 (by norm_num)
  have hq : t.val^(-5/8 : ℝ) ≤ t.val^(-7/8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge t.property.1 ht1 (by norm_num)
  rw [he]
  change ‖(l t x-actualResidual hα A b t (initial hT₀) d x-v x)-
    (l t y-actualResidual hα A b t (initial hT₀) d y-v y)‖ ≤ _
  calc
    _ = ‖(l t x-l t y)-(actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y)-(v x-v y)‖ := by congr 1; ring
    _ ≤ ‖l t x-l t y‖+‖actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y‖+‖v x-v y‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ H*‖x-y‖^γ+C*‖d‖*t.val^(-7/8 : ℝ)*‖x-y‖^γ+
      (C*‖j‖)*t.val^(-5/8 : ℝ)*Q*‖x-y‖^γ := add_le_add (add_le_add (hl t x y) hd) hv
    _ ≤ H*t.val^(-7/8 : ℝ)*‖x-y‖^γ+C*‖d‖*t.val^(-7/8 : ℝ)*‖x-y‖^γ+
      (C*‖j‖)*t.val^(-7/8 : ℝ)*Q*‖x-y‖^γ := by gcongr; exact le_mul_of_one_le_right hH hp
    _ = _ := by ring
end HolderResidualIntegralGamma

section ContDiffDuhamelOfHolderGamma
open FrozenParametrix StrongWeightedVolterra BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (A : C(Slab T,V →ᵇ Icc α β)) (hT : 0 ≤ T) (hα : 0 < α)
include hT in
lemma contDiff_duhamel_of_holder_gamma (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hj : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^γ)
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
        (H*s^(-(7/8 : ℝ)))*‖x-y‖^γ := by
    intro s hs x y
    change ‖unweighted j s x-unweighted j s y‖ ≤ _
    simpa only [neg_div] using hj ⟨s,hs.1,hs.2.le.trans t.property.2⟩ x y
  have he := funext (duhamel_eq_sourceDuhamel A hT hα j t)
  rw [he]
  exact WeightedSourceFrozenRows.contDiff_duhamel (heatKernel 1 zero_lt_one) (extendedA A hT)
    (continuous_extendedA A hT) α β hα (extendedA_range A hT) L hL (extendedA_lipschitz A hT L hLip)
    (fun s => (unweighted j s).toBCF) hf (3/4) (7/8) ‖j‖ H γ t.val
    (by norm_num) (by norm_num) (norm_nonneg j) hH t.property.1 hγ hγ1 hn hh
end ContDiffDuhamelOfHolderGamma
section SourceCorrectionHolder
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
lemma source_correction_holder (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1/4)
    (d : C₀(V,ℂ)) (l j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^γ)
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = l t-actualResidual hα A b t (initial hT₀) d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Time T, ∀ x y,
      ‖unweighted j t.val x-unweighted j t.val y‖ ≤ D*t.val^(-7/8 : ℝ)*‖x-y‖^γ := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_holder_bound hα A b hT L B hL hB hb hLip hLipb γ hγ (by linarith)
  apply correction_holder_gamma hα A b hT₀ hT C hC _ d l j H hH hl hi hj
  intro t s hst f x y
  apply (hR t s hst f x y).trans
  have hp : (t.val-s.val)^(-(3+2*γ)/4) ≤ (t.val-s.val)^(-7/8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hst)
      (by linarith [t.property.2,s.property.1]) (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (norm_nonneg f)))
    (Real.rpow_nonneg (norm_nonneg _) _)
end SourceCorrectionHolder
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β))
lemma contDiff_mildTime_of_holder_gamma (hT : 0 ≤ T)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hj : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^γ)
    (t : Time T) : ContDiff ℝ 4 (fun x => mildTime hα A hT d j t.val x) := by
  have h0 : ContDiff ℝ 4 (fun x => c0Time hα (A (initial hT)) t.val d x) := by
    rw [funext (c0Time_apply hα (A (initial hT)) t.val t.property.1 d)]
    exact contDiff_infty.mp (contDiff_timeValue hα (A (initial hT)).toContinuousMap t.val t.property.1 d) 4
  exact h0.add (contDiff_duhamel_of_holder_gamma A hT hα γ hγ hγ1 L hL hLip j H hH hj t)
end ParametrixVolterra

end

end OAI
