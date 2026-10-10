import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialRate

namespace OAI

/-! # One logarithmic coordinate rate for both neighboring suffixes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual box product estimate supplies logarithms of the suffix and
its product with the neighboring step, with a single vanishing coordinate
rate. No separate product-suffix error estimate is assumed. -/
theorem exists_neighbor_suffix_coordinate_rate
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hspos : ∀ n, 0 < scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ k : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n)) :
    ∃ (v₀ v₁ : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ),
      (∀ n, F.ExpN (F.N.equiv (v₀ n)) = k₀ n) ∧
      (∀ n, F.ExpN (F.N.equiv (v₁ n)) = k₀ n * k n) ∧
      (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (v₀ n)‖ ≤
          Real.exp (scale n * ε n) ∧
        ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (v₁ n)‖ ≤
          Real.exp (scale n * ε n) := by
  obtain ⟨C, hC, hproduct⟩ := M.exists_groupBox_product_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN b₀
  let P := fun n => C * (1 + (2 : ℝ)) ^ M.bound * (1 + R n) ^ M.bound
  have hP0 n : 0 ≤ P n := by
    have := hR0 n
    dsimp only [P]
    positivity
  have hP : HasSubexponentialUpperBoundSeq scale P := by
    apply (sequence_subexponential_upper_const hs (C * (1 + (2 : ℝ)) ^ M.bound)).mul
      (((sequence_subexponential_upper_const hs 1).add hR hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound)
    exact Eventually.of_forall (fun _ => mul_nonneg hC (by positivity))
  have hk₁ n : k₀ n * k n ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (P n) := by
    have hg : ∀ i : Fin 2, ![k₀ n, k n] i ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
      intro i
      fin_cases i
      · exact hk₀ n
      · exact hk n
    simpa [P, List.ofFn_succ] using
      hproduct E β hβ (scale n) (hspos n).le 2 (R n) (hR0 n) ![k₀ n, k n] hg
  choose v₀ hv₀ hb₀ using hk₀
  choose v₁ hv₁ hb₁ using hk₁
  obtain ⟨ε, hε0, hε, hb⟩ := exists_sequence_subexponential_rate scale
    (fun n => R n + P n) hspos (hR.add hP hs)
  refine ⟨v₀, v₁, ε, hv₀, hv₁, hε0, hε, ?_⟩
  intro n
  exact ⟨(hb₀ n).trans ((le_add_of_nonneg_right (hP0 n)).trans (hb n)),
    (hb₁ n).trans ((le_add_of_nonneg_left (hR0 n)).trans (hb n))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
