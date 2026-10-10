import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The two conjugations in a coupled recurrence remain in one source box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

include hExp in
theorem exists_sequence_double_conjugate_box
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (k₀ k g : N),
        k₀ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        k ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        k₀ * (k * g * k⁻¹) * k₀⁻¹ ∈
          M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let V := fun n => C * 6 ^ M.bound * (1 + R n) ^ M.bound
  have hp := ((sequence_subexponential_upper_const hs 1).add hR hs).pow hs
    (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound
  refine ⟨V, fun n => by have := hR0 n; dsimp [V]; positivity,
    (sequence_subexponential_upper_const hs (C * 6 ^ M.bound)).mul hp
      (Eventually.of_forall (fun _ => by positivity)), ?_⟩
  intro n k₀ k g hk₀ hk hg
  have hki := M.groupBox_inv_mem T hunimod eW eN Exp hExp E β (scale n) (R n) hk
  have hk₀i := M.groupBox_inv_mem T hunimod eW eN Exp hExp E β (scale n) (R n) hk₀
  have hv := hprod E β hβ (scale n) (hscale n) 5 (R n) (hR0 n)
    ![k₀, k, g, k⁻¹, k₀⁻¹] (by intro i; fin_cases i <;> assumption)
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, mul_one, mul_assoc,
    Nat.cast_ofNat, V, show (1 : ℝ) + 5 = 6 from by norm_num] using hv

end PolycyclicRecognition.CartanWordModel

end

end OAI
