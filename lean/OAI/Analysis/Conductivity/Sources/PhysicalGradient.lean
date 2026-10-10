import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalOpenVoltage
import OAI.Analysis.Conductivity.Sobolev.OriginalSmoothMultiplier
import OAI.Analysis.Conductivity.Variational.OriginalGradientLocality

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
attribute [local instance] Classical.propDecidable
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma source_patch_gradient {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (q W : H1) (j : Fin 2)
    (hv : ∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue q x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x)) :
    ∀ᵐ x∂ballMeasure,weakGradient W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakGradient q x else 0 := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let U : Set R3 := E ⁻¹' physicalOpenBlock
  have hU : IsOpen U := physicalOpenBlock_open.preimage E.continuous
  have hUb : U⊆ball := fun x hx => physicalOpenBlock_subset_ball hx
  have hinside : ∀ᵐ x∂ballMeasure,x∈U → weakGradient W x=weakGradient q x := by
    apply original_local_value_difference_gradient W q hU hUb (-z.terminalValue 0 j)
    filter_upwards [hv] with x hx hm
    change WithLp.ofLp x∈physicalOpenBlock at hm
    rw [hx,ite_eq_left hm]
    ring
  let O : Set R3 := ball∩{x | terminalTime 0 (E x)<0}
  have hO : IsOpen O := Metric.isOpen_ball.inter
    (isOpen_lt ((terminalTime_locallyLipschitz 0).continuous.comp E.continuous) continuous_const)
  have hout : ∀ᵐ x∂ballMeasure,x∈O → weakGradient W x=0 := by
    apply original_local_constant_gradient W hO inter_subset_left 0
    filter_upwards [hv] with x hx hm
    have hn : E x∉physicalOpenBlock := by
      intro hh
      have hh := (sourceOpenBlock_time_iff (E x)).mp hh
      exact (not_lt.mpr hm.2.le) hh.1
    change WithLp.ofLp x∉physicalOpenBlock at hn
    rw [hx,ite_eq_right hn]
    exact z.terminalProfile_zero_outside hη hηc j hm.2.le
  let C : Fin 2 → Set R3 := fun k => ball∩{x | 0<terminalTime k.succ (E x)}
  have hC (k : Fin 2) : IsOpen (C k) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const ((terminalTime_locallyLipschitz k.succ).continuous.comp E.continuous))
  have hchild (k : Fin 2) : ∀ᵐ x∂ballMeasure,x∈C k → weakGradient W x=0 := by
    apply original_local_constant_gradient W (hC k) inter_subset_left (z.terminalValue k.succ j-z.terminalValue 0 j)
    filter_upwards [hv] with x hx hm
    have hn : E x∉physicalOpenBlock := by
      intro hh
      have hh := (sourceOpenBlock_time_iff (E x)).mp hh
      exact (not_lt.mpr hm.2.le) (hh.2 k)
    change WithLp.ofLp x∉physicalOpenBlock at hn
    have hm' : 0<terminalTime k.succ (WithLp.ofLp x) := hm.2
    rw [hx,ite_eq_right hn,z.terminalProfile_child_band hη hηc j k (by linarith)]
    rw [min_eq_right hm'.le]
    ring
  have h0 := sourceColevel_ae_ne (show (0:ℝ)∈Icc (-(1:ℝ)/100) (1/100) by norm_num)
  have hh (i : Fin 3) : ∀ᵐ y : Coord3,terminalTime i y≠0 := by
    refine Fin.cases h0 (fun k => ?_) i
    exact (sourceChildInverse_quasi (actualChildSign k)).ae h0
  have hne := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (ae_all_iff.mpr hh))
  filter_upwards [hinside,hout,ae_all_iff.mpr hchild,hne,ae_restrict_mem Metric.isOpen_ball.measurableSet]
    with x hi ho hc hn hx
  by_cases hb : WithLp.ofLp x∈physicalOpenBlock
  · rw [ite_eq_left hb]
    exact hi hb
  · rw [ite_eq_right hb]
    by_cases hp : terminalTime 0 (E x)<0
    · exact ho ⟨hx,hp⟩
    · have hp' : 0<terminalTime 0 (E x) := lt_of_le_of_ne (le_of_not_gt hp) (hn 0).symm
      have hnchild : ¬∀ k : Fin 2,terminalTime k.succ (E x)<0 := by
        intro hh
        exact hb ((sourceOpenBlock_time_iff (E x)).mpr ⟨hp',hh⟩)
      push Not at hnchild
      obtain ⟨k,hk⟩ := hnchild
      exact hc k ⟨hx,lt_of_le_of_ne hk (hn k.succ).symm⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
