import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasisComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceScaleExtraction

namespace OAI

/-! # Fixed maximizing bases for affine neighboring rows -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

/-- Replace the row's varying bases by the fixed maximizing cell basis.
The original samples, profiles, law and supported affine pair are preserved. -/
def AffineNeighborRow.fixedBasis
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ) := by
  classical
  let bound := M.exists_groupBox_basis_comparison T hunimod eW b₀
  let C := Classical.choose bound
  have hC : 1 ≤ C := (Classical.choose_spec bound).1
  have hcompare := (Classical.choose_spec bound).2
  have hβ' := M.maximizing_box_basis_smul T hunimod eW b₀ hcell hne
    (show 0 ≤ 1 + δ by linarith) βcell hβ
  refine { D with
    radius := fun n => C * D.radius n
    radius_nonneg := fun n => mul_nonneg (zero_le_one.trans hC) (D.radius_nonneg n)
    radius_subexponential := ?_
    basis := fun _ => βcell
    base_mem := fun n => hcompare _ βcell (D.basis n) hβ' (D.scale n) (hs n)
      (F.ExpN ∘ F.N.equiv) (D.radius n) (D.base_mem n)
    step_mem := fun n => hcompare _ βcell (D.basis n) hβ' (D.scale n) (hs n)
      (F.ExpN ∘ F.N.equiv) (D.radius n) (D.step_mem n)
    time_bound := ?_ }
  · exact (sequence_subexponential_upper_const D.grows C).mul
      D.radius_subexponential (Eventually.of_forall fun _ => zero_le_one.trans hC)
  · intro n
    apply (D.time_bound n).trans
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left (D.radius_nonneg n) hC) (Real.exp_pos _).le

omit [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier] in
/-- The original row has a common subexponential radius in the fixed
maximizing basis, without changing any of its sampled group elements. -/
theorem AffineNeighborRow.exists_fixed_basis_radius
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq D.scale R ∧
      (∀ n, D.base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' cell) βcell (D.scale n) (R n)) ∧
      (∀ n, D.step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' cell) βcell (D.scale n) (R n)) := by
  let E := D.fixedBasis T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S hcell hne hβ hδ hs
  exact ⟨E.radius, E.radius_nonneg, E.radius_subexponential, E.base_mem, E.step_mem⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
