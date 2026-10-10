import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSubexponentialSuffixSequence
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialRate
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequenceVanishingRate

namespace OAI

/-! # Actual group chains joining allowed suffixes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include T in
/-- Both the vertices and the individual generator steps lie in one
subexponential enlargement of the original group box. The time estimate
uses precisely the original support width. -/
theorem exists_subexponential_group_chain
    [Nonempty (Fin M.letterCount)]
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
    ∃ N : ℕ, ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ (R : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale R →
      ∀ (initial increment : ℕ → cartanRootIdeal H),
      (∀ n, ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (initial n)‖ ≤ R n) →
      (∀ n, ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (increment n)‖ ≤ R n) →
      ∃ (radius : ℕ → ℝ) (vertex : ℕ → Fin (N + 1) → F.N.carrier)
        (step : ℕ → Fin N → F.N.carrier)
        (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ),
        (∀ n, 1 ≤ radius n) ∧ HasSubexponentialUpperBoundSeq scale radius ∧
        (∀ n, vertex n 0 = F.ExpN (F.N.equiv (initial n))) ∧
        (∀ n, vertex n (Fin.last N) =
          F.ExpN (F.N.equiv (initial n)) * F.ExpN (F.N.equiv (increment n))) ∧
        (∀ n j, vertex n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          E β (scale n) (radius n)) ∧
        (∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          E β (scale n) (radius n)) ∧
        (∀ n j, vertex n j.succ = vertex n j.castSucc * step n j) ∧
        (∀ n j, |time n j| ≤ radius n * Real.exp
          (scale n * (M.supportIn T hunimod eW).weightSupport E (mode n j))) ∧
        (∀ n j, F.inclusionN (step n j) =
          Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
  obtain ⟨N, C, hC, hgen⟩ := M.exists_cartan_subexponential_suffix_sequence T F
    hExp realize haarN dynkinN b₀
  obtain ⟨D, hD, hletter⟩ := M.exists_uniform_letter_groupBox_bound T hunimod eW
    (F.ExpN ∘ F.N.equiv)
  refine ⟨N, ?_⟩
  intro scale hscale hs1 R hR initial increment hinitial hincrement
  have hs0 n : 0 ≤ scale n := (by norm_num : (0 : ℝ) ≤ 1).trans (hs1 n)
  obtain ⟨ε₀, hε₀0, hε₀, hRε⟩ := exists_sequence_subexponential_rate scale R
    (fun n => lt_of_lt_of_le zero_lt_one (hs1 n)) hR
  let weights := (M.supportIn T hunimod eW).weightSupport E
  obtain ⟨ε, v, mode, time, hε0, hε, hstart, hend, hv, ht, hedge⟩ :=
    hgen weights weights hweights (fun _ => le_rfl) β β hβ hβ scale hscale hs1
      ε₀ hε₀0 hε₀ initial (fun n => (hinitial n).trans (hRε n))
      Unit (fun n _ => increment n) (fun n _ => (hincrement n).trans (hRε n))
  let K := 1 + C + C * D
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK1 : 1 ≤ K := by dsimp [K]; nlinarith [mul_nonneg hC0 hD]
  have hKC : C ≤ K := by dsimp [K]; nlinarith [mul_nonneg hC0 hD]
  have hKCD : C * D ≤ K := by dsimp [K]; linarith
  let radius : ℕ → ℝ := fun n => K * Real.exp (ε n * scale n)
  have he1 n : 1 ≤ Real.exp (ε n * scale n) := Real.one_le_exp (mul_nonneg (hε0 n) (hs0 n))
  have hr1 n : 1 ≤ radius n := by
    dsimp [radius]
    nlinarith [mul_le_mul hK1 (he1 n) zero_le_one (zero_le_one.trans hK1)]
  have hr : HasSubexponentialUpperBoundSeq scale radius :=
    (sequence_subexponential_upper_const hscale K).mul
      (sequence_subexponential_exp_of_vanishing_rate hs0 hε)
      (Eventually.of_forall (fun _ => zero_le_one.trans hK1))
  have hrad n : Real.exp (scale n * ε n) ≤ radius n := by
    dsimp [radius]
    rw [mul_comm (ε n) (scale n)]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hK1
  have htime n j : |time n () j| ≤ C * Real.exp (ε n * scale n) *
      Real.exp (scale n * weights (mode n () j)) := by
    simpa only [mul_add, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using ht n () j
  refine ⟨radius, (fun n j => F.ExpN (F.N.equiv (v n () j))),
    (fun n j => F.ExpN (F.N.equiv (time n () j • M.letter (mode n () j)))),
    (fun n j => mode n () j), (fun n j => time n () j), hr1, hr,
    (fun n => congrArg (fun z => F.ExpN (F.N.equiv z)) (hstart n ())),
    (fun n => hend n ()), ?_, ?_,
    (fun n j => hedge n () j), ?_, ?_⟩
  · intro n j
    exact ⟨v n () j, rfl, (hv n () j).trans (hrad n)⟩
  · intro n j
    obtain ⟨x, hx, hbound⟩ := hletter E hE hne β (mode n () j) (scale n)
      (C * Real.exp (ε n * scale n)) (time n () j) (hs0 n)
      (mul_nonneg hC0 (Real.exp_pos _).le) (htime n j)
    refine ⟨x, hx, hbound.trans ?_⟩
    dsimp [radius]
    calc
      C * Real.exp (ε n * scale n) * D = C * D * Real.exp (ε n * scale n) := by ring
      _ ≤ K * Real.exp (ε n * scale n) :=
        mul_le_mul_of_nonneg_right hKCD (Real.exp_pos _).le
  · intro n j
    exact (htime n j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC (Real.exp_pos _).le) (Real.exp_pos _).le)
  · intro n j
    change F.inclusionN (F.ExpN (F.N.equiv (time n () j • M.letter (mode n () j)))) = _
    rw [F.compatibleN]
    rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
