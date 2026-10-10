import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.SphereProjection

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff
namespace YauCounterexamples

lemma exists_box_Icc_subset_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ I : Box ι, Box.Icc I ⊆ U := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let I : Box ι := ⟨fun i => x i-ε/2,fun i => x i+ε/2,fun i => by linarith⟩
  refine ⟨I,?_⟩
  intro y hy
  have hd : dist y x ≤ ε/2 := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs]
    have h₁ : x i-ε/2 ≤ y i := hy.1 i
    have h₂ : y i ≤ x i+ε/2 := hy.2 i
    exact abs_le.mpr ⟨by dsimp; linarith,by dsimp; linarith⟩
  exact hball (hd.trans_lt (by linarith))

theorem exists_spherical_sign_box :
    ∃ I : Box (Fin 3), ∀ y ∈
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm '' Box.Icc I,
      (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) ∧
      sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < 1/8 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let f : (Fin 3 → ℝ) → ℝ := fun x =>
    sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) sourcePole).symm (e x))
  have hf : Continuous f := (sphericalRadius_continuous _ _).comp
    ((sphere_chart_symm_continuous sourcePole).comp e.continuous)
  have hsrc : sourceSignPoint ∈ (chartAt (Euclidean 3) sourcePole).source := by
    apply sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (R := 1/8) (by norm_num)
    change sphericalRadius sourceAxisOne sourceAxisTwo sourceSignPoint ≤ 1/8
    rw [sphericalRadius_sourceSignPoint]
    norm_num
  have hn : (f ⁻¹' Set.Ioo (1/20 : ℝ) (1/8)).Nonempty := by
    refine ⟨e.symm ((chartAt (Euclidean 3) sourcePole) sourceSignPoint),?_⟩
    change 1/20 < f _ ∧ f _ < 1/8
    dsimp [f]
    rw [e.apply_symm_apply,(chartAt (Euclidean 3) sourcePole).left_inv hsrc,
      sphericalRadius_sourceSignPoint]
    norm_num
  obtain ⟨I,hI⟩ := exists_box_Icc_subset_open (isOpen_Ioo.preimage hf) hn
  refine ⟨I,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact hI hx

end YauCounterexamples

end

end OAI
