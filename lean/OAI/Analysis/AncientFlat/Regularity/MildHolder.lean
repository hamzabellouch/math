import OAI.Analysis.AncientFlat.Weighted.WeightedHolder
import OAI.Analysis.AncientFlat.Regularity.FrozenHolder
import OAI.Analysis.AncientFlat.Regularity.GammaBoundedJets

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra BiharmonicKernel SourceFrozenRows
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
lemma fourth_holder_mildTime_of_holder (hα : 0<α) (A : C(Slab T,V →ᵇ Icc α β))
    (hT₀ : 0≤T) (hT : T≤1) (γ p L : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (hp₀ : 0≤p) (hp : p<1) (hL : 0≤L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s.val-r.val|))
    (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0≤H)
    (hhold : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖≤H*s.val^(-p)*‖x-y‖^γ)
    (a : ℝ) (ha : 0<a) :
    (∀ t∈Ioc 0 T, ContDiff ℝ 4 (fun x => mildTime hα A hT₀ d j t x)) ∧
    ∃ C : ℝ, 0≤C ∧
      (∀ t∈Icc a T, ∀ x, ‖iteratedFDeriv ℝ 4 (fun y => mildTime hα A hT₀ d j t y) x‖≤C) ∧
      (∀ t∈Icc a T, ∀ s∈Icc a T, ∀ x y,
        ‖iteratedFDeriv ℝ 4 (fun z => mildTime hα A hT₀ d j t z) x-
          iteratedFDeriv ℝ 4 (fun z => mildTime hα A hT₀ d j s z) y‖≤C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  let : NormedAddCommGroup (Time T →ᵇ C₀(V,ℂ)) := inferInstance
  have hf : StronglyMeasurable (fun s => (unweighted j s).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_stronglyMeasurable (stronglyMeasurable_unweighted j)
  have hfn : ∀ s∈Ioo 0 T, ‖(unweighted j s).toBCF‖≤‖j‖*s^(-(3/4:ℝ)) := by
    intro s hs
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    simpa only [neg_div,mul_comm] using norm_unweighted_le j s hs.1
  have hfh : ∀ s∈Ioo 0 T, ∀ x y : V,
      ‖(unweighted j s).toBCF x-(unweighted j s).toBCF y‖≤H*s^(-p)*‖x-y‖^γ := by
    intro s hs x y
    exact hhold ⟨s,hs.1,hs.2.le⟩ x y
  obtain ⟨hu,C,hC,hcn,hch⟩ := weighted_fourth_derivative_holder
    (heatKernel 1 zero_lt_one) (extendedA A hT₀) (continuous_extendedA A hT₀)
    α β γ L (3/4) p ‖j‖ H T hα hγ hγ1 hL (extendedA_range A hT₀)
    (extendedA_lipschitz A hT₀ L hLip) (by norm_num) (by norm_num) hp₀ hp (norm_nonneg j) hH hT
    (fun s => (unweighted j s).toBCF) hf hfn hfh a ha
  let A0 : V → ℝ := fun y => (A (initial hT₀) y).val
  have hA0 : Continuous A0 := continuous_subtype_val.comp (A (initial hT₀)).continuous
  have hA0r : ∀ y,A0 y∈Icc α β := fun y => (A (initial hT₀) y).property
  have hA0L : ∀ x y, ‖A0 x-A0 y‖≤L*‖x-y‖ := by
    intro x y
    simpa only [A0,Real.norm_eq_abs,sub_self,abs_zero,add_zero] using hLip (initial hT₀) (initial hT₀) x y
  obtain ⟨B,hB,hbn,hbh⟩ := VariableSchauder.frozen_fourth_holder (heatKernel 1 zero_lt_one)
    A0 hA0 α β L γ a T hα hL hγ hγ1 ha hT hA0r hA0L d.toBCF
  have h0 (t) (ht : t∈Ioc 0 T) : ContDiff ℝ 4 (fun x => c0Time hα (A (initial hT₀)) t d x) := by
    rw [funext (c0Time_eq_sourceValue hα _ _ ht.1 d)]
    exact contDiff_infty.mp (contDiff_value (heatKernel 1 zero_lt_one) _ hA0 α β hα hA0r
      _ (Real.rpow_pos_of_pos ht.1 _) d.toBCF) 4
  have h1 (t) (ht : t∈Ioc 0 T) : ContDiff ℝ 4 (fun x => ParametrixVolterra.duhamel hα A j t x) := by
    rw [funext (duhamel_eq_sourceDuhamel A hT₀ hα j ⟨t,ht⟩)]
    exact hu t ht
  constructor
  · intro t ht
    exact (h0 t ht).add (h1 t ht)
  have heq (t) (ht : t∈Icc a T) (x : V) :
      iteratedFDeriv ℝ 4 (fun y => mildTime hα A hT₀ d j t y) x=
        VariableSchauder.jet (heatKernel 1 zero_lt_one) A0 t d.toBCF 4 x+
          iteratedFDeriv ℝ 4 (SourceFrozenRows.duhamel (heatKernel 1 zero_lt_one)
            (extendedA A hT₀) (fun s => (unweighted j s).toBCF) t) x := by
    have ht' : t∈Ioc 0 T := ⟨ha.trans_le ht.1,ht.2⟩
    change iteratedFDeriv ℝ 4 (fun y => c0Time hα (A (initial hT₀)) t d y+
      ParametrixVolterra.duhamel hα A j t y) x=_
    rw [fun_iteratedFDeriv_add (h0 t ht') (h1 t ht'),iteratedFDeriv_c0Time hα _ _ ht'.1 d]
    dsimp only
    rw [timeBCF_apply,funext (duhamel_eq_sourceDuhamel A hT₀ hα j ⟨t,ht'⟩)]
    rfl
  refine ⟨B+C,add_nonneg hB hC,?_,?_⟩
  · intro t ht x
    rw [heq t ht x]
    exact (norm_add_le ..).trans (add_le_add (hbn t ht x) (hcn t ht x))
  · intro t ht s hs x y
    rw [heq t ht x,heq s hs y]
    have he : ∀ u v w z : V [×4]→L[ℝ] ℂ, ‖u+v-(w+z)‖≤‖u-w‖+‖v-z‖ := by
      intro u v w z; rw [show u+v-(w+z)=(u-w)+(v-z) by abel]; exact norm_add_le ..
    exact (he _ _ _ _).trans ((add_le_add (hbh t ht s hs x y) (hch t ht s hs x y)).trans_eq (by ring))
end ParametrixVolterra

end

end OAI
