import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileAnchors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialRate
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # A fixed metric bound for every allowed suffix family -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include T in
/-- The bound is fixed before the enlargement, the scale sequence, and
the subexponential radius. Thus compact profiles may be chosen before the
small enlargement required by the neighboring theorem. -/
theorem exists_uniform_suffix_metric_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ (scale R : ℕ → ℝ), (∀ n, 1 ≤ scale n) →
      HasSubexponentialUpperBoundSeq scale R →
      ∀ᶠ n in atTop, ∀ k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' E) β (scale n) (R n),
      ∀ q ∈ (fun u => u * k) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1,
        dist 1 (F.inclusionN q) / scale n ≤ C := by
  let s := (M.supportIn T hunimod eW).weightSupport E
  let t := fun i => 2 * s i
  have ht i : 0 < t i := mul_pos (by norm_num) (hweights i)
  have hβt : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [columnBasisWeight, t, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by norm_num)
  obtain ⟨C, lo, hC, hlo, hanchor⟩ := exists_bounded_box_profile_anchors T M F
    hExp realize haarN dynkinN b₀ s t hweights ht
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 scale R hs1 hR
  have hs0 n : 0 ≤ scale n := zero_le_one.trans (hs1 n)
  obtain ⟨ε, _, hε, hRε⟩ := exists_sequence_subexponential_rate scale R
    (fun n => zero_lt_one.trans_le (hs1 n)) hR
  filter_upwards [hε.eventually (gt_mem_nhds hlo)] with n hn
  intro k hk q hq
  obtain ⟨u, hu, rfl⟩ := hq
  apply hanchor β β hβ hβt (scale n) (ε n) (hs1 n) hn.le u k hu
  obtain ⟨v, hv, hcoord⟩ := hk
  refine ⟨v, hv, le_trans ?_ (hRε n)⟩
  have hcost (w : M.wordList) : M.boxCost T hunimod eW ((fun w => (1 + δ) • w) '' E) w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  change ‖(M.boxBasis T hunimod eW ((fun w => (1 + δ) • w) '' E) β (scale n)).equivFun v‖
    ≤ R n at hcoord
  simp only [boxBasis, hcost] at hcoord
  have hgain := norm_change_exponentialRescaleBasis_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => 2 * M.boxCost T hunimod eW E (β.val j))
    (fun j => (1 + δ) * M.boxCost T hunimod eW E (β.val j)) (hs0 n) (α := 0)
    (fun j => by
      have hp : 0 ≤ M.boxCost T hunimod eW E (β.val j) :=
        (bracketWordExponent_pos s hweights _).le
      nlinarith [mul_le_mul_of_nonneg_right hδ1 hp]) v
  simp only [mul_zero, Real.exp_zero, one_mul] at hgain
  simpa only [t, bracketWordExponent_const_mul, boxCost, s] using hgain.trans hcoord

end PolycyclicRecognition.CartanWordModel

end

end OAI
