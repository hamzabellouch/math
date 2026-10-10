import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowProfile
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanReverseNeighborLaw

namespace OAI

/-! # Reversing the original affinity row -/

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

/-- The opposite trace inequality uses an actual row with the same root
and the two labels and offsets swapped. Only its subexponential radius changes. -/
theorem AffineNeighborRow.exists_reverse
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    ∃ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ),
      R.scale = D.scale ∧ R.mode = D.mode ∧
      R.label₁ = D.label₂ ∧ R.label₂ = D.label₁ ∧
      R.offset₁ = D.offset₂ ∧ R.offset₂ = D.offset₁ := by
  let D' := D.fixedBasis T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S hcell hne hβ hδ hs
  have hβ' := M.maximizing_box_basis_smul T hunimod eW b₀ hcell hne
    (show 0 ≤ 1 + δ by linarith) βcell hβ
  obtain ⟨R, hRR, hR0, hR, hbounds⟩ := M.exists_reverse_neighbor_radius T F hunimod eW
    dynkinN b₀ ((fun w => (1 + δ) • w) '' cell) βcell hβ' D'.scale D'.radius
    D'.grows hs D'.radius_nonneg D'.radius_subexponential D'.base D'.step
    D'.base_mem D'.step_mem
  let g := D'.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S
  obtain ⟨hg, hactual, hlaw⟩ := D'.gluedProfile_properties T M F hunimod eW π b₀
    cell βcell X βD haarN chartN hchartN pivot shrink B δ S
  have hreverse := M.reversed_neighbor_cell_limit T F hunimod eW haarN chartN hchartN
    b₀ cell βcell D'.scale D'.base D'.step g hg D'.law hlaw
  refine ⟨{
    scale := D'.scale
    grows := D'.grows
    pair := D'.pair
    center := D'.center
    radius := R
    radius_nonneg := hR0
    radius_subexponential := hR
    base := fun n => D'.base n * D'.step n
    step := fun n => (D'.step n)⁻¹
    basis := fun _ => βcell
    base_mem := fun n => (hbounds n).1
    step_mem := fun n => (hbounds n).2
    mode := D'.mode
    time := fun n => -D'.time n
    time_bound := ?_
    root_step := fun n => M.inverse_root_step F hExp D'.mode (D'.step n)
      (D'.time n) (D'.root_step n)
    profile := fun n q => (g n q, g n (q * (D'.step n)⁻¹))
    measurable_profile := fun n => (hg n).prodMk ((hg n).comp
      (continuous_id.mul continuous_const).measurable)
    actual := ?_
    law := ProbabilityMeasure.map D'.law Prod.swap
    converges := hreverse
    point := D'.point.swap
    supported := swapped_pair_mem_support D'.law D'.supported
    label₁ := D'.label₂
    label₂ := D'.label₁
    offset₁ := D'.offset₂
    offset₂ := D'.offset₁
    affine₁ := D'.affine₂
    affine₂ := D'.affine₁ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro n
    rw [abs_neg]
    exact (D'.time_bound n).trans
      (mul_le_mul_of_nonneg_right (hRR n) (Real.exp_pos _).le)
  · intro n q hq z
    obtain ⟨v, hv, rfl⟩ := hq
    constructor
    · apply hactual n _ (Or.inr ⟨v * D'.base n, ⟨v, hv, rfl⟩, mul_assoc _ _ _⟩) z
    · apply hactual n _ (Or.inl ?_) z
      refine ⟨v, hv, ?_⟩
      simp [mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
