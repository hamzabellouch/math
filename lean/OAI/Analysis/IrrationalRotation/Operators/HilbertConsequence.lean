import OAI.Analysis.IrrationalRotation.Operators.HyperinvariantProjection
import OAI.Analysis.IrrationalRotation.Analysis.UnitaryTransport
import OAI.Analysis.IrrationalRotation.Operators.CommutantAlgebra
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentNonscalar
import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Operators.HilbertModelSize
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

noncomputable section
namespace Invariant233

open scoped Topology
open TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

theorem no_hyperinvariant_subspace_of_no_invariant_projection
    (M : VonNeumannAlgebra E) {T : E →L[ℂ] E} (hT : T ∈ M)
    (hproj : ∀ p : E →L[ℂ] E, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    ∀ S : Submodule ℂ E, IsClosed (S : Set E) →
      (∀ A : E →L[ℂ] E, Commute A T → ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS hhyper
  let : CompleteSpace S := hS.completeSpace_coe
  have hhyper' : ∀ A : E →L[ℂ] E, Commute A T → S ∈ Module.End.invtSubmodule A :=
    hhyper
  obtain ⟨hmem, hinv⟩ := hyperinvariant_subspace_projection_mem M hT S hhyper'
  rcases hproj S.starProjection hmem isStarProjection_starProjection hinv with hzero | hone
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have heq := Submodule.starProjection_eq_self_iff.mpr hx
    simpa [hzero] using heq.symm
  · right
    apply le_antisymm le_top
    intro x _
    apply Submodule.starProjection_eq_self_iff.mp
    simp [hone]

theorem hilbert_counterexample_of_factor_witness
    [SeparableSpace E] [SeparableSpace F]
    (hE : ¬ FiniteDimensional ℂ E) (hF : ¬ FiniteDimensional ℂ F)
    (M : VonNeumannAlgebra E) {T : E →L[ℂ] E} (hT : T ∈ M) (hne : T ≠ 0)
    (hquasi : Filter.Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ)))
      Filter.atTop (𝓝 (0 : ℝ)))
    (hproj : ∀ p : E →L[ℂ] E, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    ∃ T' : F →L[ℂ] F, T' ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ => ‖T' ^ n‖ ^ (1 / (n : ℝ)))
        Filter.atTop (𝓝 (0 : ℝ)) ∧
      (∀ S : Submodule ℂ F, IsClosed (S : Set F) →
        (∀ A : F →L[ℂ] F, Commute A T' → ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤) := by
  obtain ⟨e⟩ := UnitaryTransport.nonempty_linearIsometryEquiv hE hF
  exact UnitaryTransport.transport_counterexample e T hne hquasi
    (no_hyperinvariant_subspace_of_no_invariant_projection M hT hproj)

theorem hasNoNontrivialHyperinvariantSubspace_of_no_invariant_projection
    (M : VonNeumannAlgebra E) {T : E →L[ℂ] E} (hT : T ∈ M)
    (hproj : ∀ p : E →L[ℂ] E, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    HasNoNontrivialHyperinvariantSubspace T := by
  intro S hS
  apply no_hyperinvariant_subspace_of_no_invariant_projection M hT hproj S hS.1
  intro A hA
  apply hS.2 A
  exact (operatorCommutant_mem_iff T A).2 hA.symm.eq

theorem transitive_commutant_of_factor_witness
    [SeparableSpace E] [SeparableSpace F]
    (hE : ¬ FiniteDimensional ℂ E) (hF : ¬ FiniteDimensional ℂ F)
    (M : VonNeumannAlgebra E) {T : E →L[ℂ] E} (hT : T ∈ M) (hne : T ≠ 0)
    (hquasi : NormQuasinilpotent T)
    (hproj : ∀ p : E →L[ℂ] E, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    ∃ T' : F →L[ℂ] F, T' ≠ 0 ∧ NormQuasinilpotent T' ∧
      HasNoNontrivialHyperinvariantSubspace T' ∧
      operatorCommutant T' ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T') ∧
      IsTransitive (operatorCommutant T') := by
  classical
  have : Nontrivial F := by
    cases subsingleton_or_nontrivial F with
    | inl h =>
      let : Subsingleton F := h
      exact False.elim (hF inferInstance)
    | inr h => exact h
  obtain ⟨T', hne', hquasi', hhyper'⟩ :=
    hilbert_counterexample_of_factor_witness hE hF M hT hne hquasi hproj
  have hnonscalar : ¬ ∃ c : ℂ, T' = c • (1 : F →L[ℂ] F) := by
    rintro ⟨c, hc⟩
    exact InvariantProjection.continuousLinearMap_not_scalar_of_nonzero_norm_root_tendsto
      hne' hquasi' c hc
  have hhyper : HasNoNontrivialHyperinvariantSubspace T' := by
    intro S hS
    apply hhyper' S hS.1
    intro A hA
    exact hS.2 A ((operatorCommutant_mem_iff T' A).2 hA.symm.eq)
  obtain ⟨hproper, hclosed, htrans⟩ := commutant_algebra_properties T' hnonscalar
  exact ⟨T', hne', hquasi', hhyper, hproper, hclosed, htrans.2 hhyper⟩

theorem transitive_commutant_of_circle_witness
    [SeparableSpace F] (hF : ¬ FiniteDimensional ℂ F)
    (M : VonNeumannAlgebra (MeasureTheory.Lp (lp (fun _ : ℤ => ℂ) 2) 2 circleMeasure))
    {T : (MeasureTheory.Lp (lp (fun _ : ℤ => ℂ) 2) 2 circleMeasure) →L[ℂ]
      (MeasureTheory.Lp (lp (fun _ : ℤ => ℂ) 2) 2 circleMeasure)}
    (hT : T ∈ M) (hne : T ≠ 0) (hquasi : NormQuasinilpotent T)
    (hproj : ∀ p : (MeasureTheory.Lp (lp (fun _ : ℤ => ℂ) 2) 2 circleMeasure) →L[ℂ]
        (MeasureTheory.Lp (lp (fun _ : ℤ => ℂ) 2) 2 circleMeasure),
      p ∈ M → IsStarProjection p → (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    ∃ T' : F →L[ℂ] F, T' ≠ 0 ∧ NormQuasinilpotent T' ∧
      HasNoNontrivialHyperinvariantSubspace T' ∧
      operatorCommutant T' ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T') ∧
      IsTransitive (operatorCommutant T') := by
  let := HilbertModelSize.circle_representation_separable
  exact transitive_commutant_of_factor_witness
    HilbertModelSize.circle_representation_not_finiteDimensional hF M hT hne hquasi hproj

end Invariant233

end

end OAI
