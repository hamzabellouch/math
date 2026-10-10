import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergy

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonApprox

attribute [local instance] Classical.propDecidable

open Set Metric CannonCrossEnergy

lemma meshEnergy_eq_sum_filter {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) :
    meshEnergy p r J F K = ∑ i ∈ Finset.univ.filter
      (fun i => (ball (p i) (2*r) ∩ K).Nonempty),
      (oscillation F (closedBall (p i) (J*r)))^2 := by
  classical
  simpa only [meshEnergy, Finset.subtype_univ] using (Finset.sum_subtype_eq_sum_filter
    (s := Finset.univ) (p := fun i => (ball (p i) (2*r) ∩ K).Nonempty)
    (f := fun i => (oscillation F (closedBall (p i) (J*r)))^2))

lemma meshEnergy_mono_set {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) {K L : Set X} (hKL : K ⊆ L) :
    meshEnergy p r J F K ≤ meshEnergy p r J F L := by
  classical
  rw [meshEnergy_eq_sum_filter,meshEnergy_eq_sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact hi.mono (inter_subset_inter_right _ hKL)
  · intro i _ _
    exact sq_nonneg _

lemma oscillation_mono_of_bounded {X : Type*} (f : X → ℝ)
    (hhi : BddAbove (range f)) (hlo : BddBelow (range f))
    {A B : Set X} (hA : A.Nonempty) (hAB : A ⊆ B) :
    0 ≤ oscillation f A ∧ oscillation f A ≤ oscillation f B := by
  have hAn := hA.image f
  have hhiA := hhi.mono (image_subset_range f A)
  have hloA := hlo.mono (image_subset_range f A)
  have hhiB := hhi.mono (image_subset_range f B)
  have hloB := hlo.mono (image_subset_range f B)
  exact ⟨sub_nonneg.mpr (csInf_le_csSup hAn hloA hhiA),
    sub_le_sub (csSup_le_csSup hhiB hAn (image_mono hAB))
      (csInf_le_csInf hloB hAn (image_mono hAB))⟩

lemma meshEnergy_mono_radius {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r : ℝ) (hr : 0 ≤ r) (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (K : Set X) {J T : ℝ} (hJ : 0 ≤ J) (hJT : J ≤ T) :
    meshEnergy p r J F K ≤ meshEnergy p r T F K := by
  classical
  apply Finset.sum_le_sum
  intro i _
  have hh := oscillation_mono_of_bounded F hhi hlo
    (nonempty_closedBall.mpr (mul_nonneg hJ hr) :
      (closedBall (p i.val) (J*r)).Nonempty)
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hJT hr))
  exact pow_le_pow_left₀ hh.1 hh.2 2

end CannonApprox

end
end
end
end
end
end
end
end
end
end

end OAI
