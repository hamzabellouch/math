import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSupportSwitch
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel

namespace OAI

/-! # One switch constant for the actual Cartan alphabet

The finite family of nonzero root generators admits one logarithmic switch
bound. At a supporting position, the large generator amplitude cancels the
scalar part of the adjoint action exactly.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)

include T in
/-- Uniformly short supporting switches for every letter in the constructed
Cartan word model, including its generalized-root nilpotent corrections. -/
theorem exists_uniform_support_switch_bound
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin M.letterCount) (r : ℝ), 0 ≤ r →
      ∀ (x : G) (h : H) (s t : ℝ),
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      M.weight i h = r * s → |t| ≤ B * Real.exp (r * s) →
      dist (x * Exp h) (x * Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤
        K * Real.log (2 + r) := by
  classical
  let X (i : Fin M.letterCount) : rootSpace H (M.weight i) :=
    ⟨M.letter i, M.letter_root i⟩
  choose K hK hb using (fun i : Fin M.letterCount =>
    logarithmic_root_support_switch_polynomial_position T H (M.weight i)
      (M.weight_nonzero i) Exp hExp realize (X i) hA hB p)
  let K' := 1 + ∑ i, K i
  have hnonneg i : 0 ≤ K i := (hK i).le
  have hK' : 0 < K' := by
    have hh : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hnonneg i)
    dsimp [K']
    linarith
  refine ⟨K', hK', ?_⟩
  intro i r hr x h s t hh hs ht
  have hcancel : |t| * Real.exp (-(M.weight i h)) ≤ B := by
    rw [hs]
    have ht' := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-(r * s))).le
    have he : Real.exp (r * s) * Real.exp (-(r * s)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simpa only [mul_assoc, he, mul_one] using ht'
  have hki : K i ≤ K' := by
    have hi : K i ≤ ∑ j, K j :=
      Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    dsimp [K']
    linarith
  exact (hb i r hr x h t hh hcancel).trans
    (mul_le_mul_of_nonneg_right hki (Real.log_nonneg (by linarith)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
