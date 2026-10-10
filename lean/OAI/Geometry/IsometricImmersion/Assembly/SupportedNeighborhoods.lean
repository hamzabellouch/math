import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import Mathlib.Analysis.LocallyConvex.WithSeminorms

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def perturbationSeminormFamily : ℕ → Seminorm ℝ SymmetricPerturbation := fun k =>
  (ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k).comp
    symmetricSupportedSubmodule.subtype

theorem perturbationSeminormFamily_apply (k : ℕ) (η : SymmetricPerturbation) :
    perturbationSeminormFamily k η = perturbationSeminorm k η := rfl

theorem symmetricPerturbation_withSeminorms : WithSeminorms perturbationSeminormFamily :=
  Topology.IsInducing.withSeminorms
    (ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact)
    (f := symmetricSupportedSubmodule.subtype) .subtypeVal

theorem exists_finite_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (s : Finset ℕ) (epsilon : ℝ), 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k ∈ s, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ :=
    (symmetricPerturbation_withSeminorms.mem_nhds_iff η O).mp (hO.mem_nhds hη)
  refine ⟨s, epsilon, heps, ?_⟩
  intro ρ hρ
  apply hsub
  rw [Seminorm.mem_ball]
  simpa only [add_sub_cancel_left] using
    Seminorm.finset_sup_apply_lt heps
      (show ∀ k ∈ s, perturbationSeminormFamily k ρ < epsilon from hρ)

theorem exists_ordered_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (N : ℕ) (epsilon : ℝ), 10 < N ∧ 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k < N, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ := exists_finite_seminorm_neighborhood hO hη
  let N : ℕ := max 11 (s.sup id + 1)
  have hN : 10 < N :=
    lt_of_lt_of_le (by norm_num : 10 < (11 : ℕ)) (le_max_left _ _)
  refine ⟨N, epsilon, hN, heps, ?_⟩
  intro ρ hρ
  apply hsub ρ
  intro k hk
  have hkSup : k ≤ s.sup id := by
    simpa only [id_eq] using (Finset.le_sup (f := id) hk)
  exact hρ k (lt_of_lt_of_le (Nat.lt_succ_of_le hkSup) (le_max_right _ _))

end SmoothLocal.Perturbation

end

end OAI
