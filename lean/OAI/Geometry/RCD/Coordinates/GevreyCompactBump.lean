import OAI.Geometry.RCD.Coordinates.GevreyExpGlue
import OAI.Geometry.RCD.Coordinates.FrozenJetTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # A compact Euclidean Gevrey bump

Products of affine copies of the flat exponential give a nonnegative
Gevrey-two function, positive at the origin, supported in a fixed small
ball. No existence theorem for Gevrey functions is assumed.
-/

open Set Metric Finset
open scoped ContDiff

noncomputable section
namespace RegularPointCoordinates

private theorem factorial_product_le {n i : ℕ} (hi : i ≤ n) :
    (n.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((n - i).factorial : ℝ) ^ 2 ≤
      (n.factorial : ℝ) ^ 2 := by
  have heq : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hchoose : (1 : ℝ) ≤ n.choose i := by exact_mod_cast Nat.choose_pos hi
  have hprod : (i.factorial : ℝ) * ((n - i).factorial : ℝ) ≤ n.factorial := by
    nlinarith [mul_nonneg (show 0 ≤ (i.factorial : ℝ) by positivity)
      (show 0 ≤ ((n - i).factorial : ℝ) by positivity)]
  calc
    _ = (n.factorial : ℝ) * ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) := by
      rw [← heq]; ring
    _ ≤ _ := by nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product estimate used to assemble the coordinate bump. -/
theorem gevreyTwo_mul_bound {f g : E → ℝ} {A : ℝ} (hA : 1 ≤ A)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : ∀ m x, ‖iteratedFDeriv ℝ m f x‖ ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2)
    (hgb : ∀ m x, ‖iteratedFDeriv ℝ m g x‖ ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2)
    (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤
      (2 * A ^ 2) ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  have hA0 := zero_le_one.trans hA
  have hterm (i : ℕ) (hi : i ∈ range (m + 1)) :
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (m - i) g x‖ ≤
      A ^ (m + 2) * (m.factorial : ℝ) ^ 2 := by
    have hi' : i ≤ m := by simpa using hi
    calc
      _ ≤ (m.choose i : ℝ) * (A ^ (i + 1) * (i.factorial : ℝ) ^ 2) *
          (A ^ (m - i + 1) * ((m - i).factorial : ℝ) ^ 2) := by
        gcongr
        · exact hfb i x
        · exact hgb (m - i) x
      _ = A ^ (m + 2) * ((m.choose i : ℝ) * (i.factorial : ℝ) ^ 2 *
          ((m - i).factorial : ℝ) ^ 2) := by
        rw [show m + 2 = (i + 1) + (m - i + 1) by omega, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_product_le hi') (by positivity)
  calc
    _ ≤ ∑ i ∈ range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (m - i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ (m + 1 : ℝ) * (A ^ (m + 2) * (m.factorial : ℝ) ^ 2) := by
      simpa using sum_le_sum hterm
    _ ≤ (2 : ℝ) ^ (m + 1) * (A ^ (2 * (m + 1)) * (m.factorial : ℝ) ^ 2) := by
      gcongr
      · exact_mod_cast (Nat.lt_two_pow_self (n := m + 1)).le
      · omega
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Finite products preserve the all-order bounds needed here. -/
theorem exists_gevreyTwo_prod_bound {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ s, ∃ A : ℝ, 1 ≤ A ∧ ∀ m x,
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m x,
      ‖iteratedFDeriv ℝ m (fun y => ∏ i ∈ s, f i y) x‖ ≤
        A ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, le_rfl, ?_⟩
    intro m x
    cases m with
    | zero => simp
    | succ m => simp [iteratedFDeriv_succ_const]
  | @insert i s his ih =>
    obtain ⟨A, hA, hAb⟩ := hb i (mem_insert_self _ _)
    obtain ⟨B, hB, hBb⟩ := ih
      (fun j hj => hf j (mem_insert_of_mem hj))
      (fun j hj => hb j (mem_insert_of_mem hj))
    let C := max A B
    have hC : 1 ≤ C := hA.trans (le_max_left _ _)
    refine ⟨2 * C ^ 2, by nlinarith [sq_nonneg C], ?_⟩
    intro m x
    simp only [prod_insert his]
    apply gevreyTwo_mul_bound hC (hf i (mem_insert_self _ _))
      (contDiff_prod fun j hj => hf j (mem_insert_of_mem hj))
    · intro k y
      exact (hAb k y).trans (by gcongr; exact le_max_left A B)
    · intro k y
      exact (hBb k y).trans (by gcongr; exact le_max_right A B)

/-- An affine flat exponential has a Gevrey-two bound. -/
theorem exists_gevreyTwo_affine_glue_bound (L : E →L[ℝ] ℝ) (a : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m x,
      ‖iteratedFDeriv ℝ m (fun y => expNegInvGlue (a + L y)) x‖ ≤
        A ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  let A : ℝ := 8 * max 1 ‖L‖
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_left 1 ‖L‖]
  refine ⟨A, hA, ?_⟩
  intro m x
  calc
    _ ≤ ‖iteratedFDeriv ℝ m expNegInvGlue (a + L x)‖ * ‖L‖ ^ m :=
      norm_iteratedFDeriv_comp_affine_le L expNegInvGlue a x m
        expNegInvGlue.contDiff.contDiffAt
    _ ≤ (8 ^ m * (m.factorial : ℝ) ^ 2) * (max 1 ‖L‖) ^ m := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      gcongr
      exact norm_iteratedDeriv_expNegInvGlue_le m (a + L x)
      exact le_max_right 1 ‖L‖
    _ = A ^ m * (m.factorial : ℝ) ^ 2 := by dsimp [A]; rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA (Nat.le_succ m))
      positivity

/-- A nonnegative compact bump with Gevrey-two jets and support in radius `1/4`. -/
theorem exists_small_gevreyTwo_bump (n : ℕ) :
    ∃ b : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < b 0 ∧ tsupport b ⊆ closedBall 0 (1 / 4) ∧
      ∃ A : ℝ, 1 ≤ A ∧ ∀ m x,
        ‖iteratedFDeriv ℝ m b x‖ ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  classical
  let S : ℝ := 8 * (n + 1)
  have hS : 0 < S := by dsimp [S]; positivity
  let L : Fin n × Bool → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun j => (if j.2 then S else -S) • EuclideanSpace.proj j.1
  let f := fun (j : Fin n × Bool) (x : EuclideanSpace ℝ (Fin n)) =>
    expNegInvGlue (1 + L j x)
  let b := fun x => ∏ j, f j x
  have hf (j : Fin n × Bool) : ContDiff ℝ ∞ (f j) :=
    expNegInvGlue.contDiff.comp (contDiff_const.add (L j).contDiff)
  have hb : ContDiff ℝ ∞ b := contDiff_prod fun j _ => hf j
  refine ⟨b, hb, fun x => prod_nonneg fun j _ => expNegInvGlue.nonneg _, ?_, ?_, ?_⟩
  · apply prod_pos
    intro j hj
    apply expNegInvGlue.pos_of_pos
    simp [L]
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hcoord (i : Fin n) : |x i| ≤ S⁻¹ := by
      have hne (j : Fin n × Bool) : f j x ≠ 0 :=
        (prod_ne_zero_iff.mp hx) j (mem_univ j)
      have hp := lt_of_not_ge ((expNegInvGlue.zero_iff_nonpos).not.mp (hne (i, true)))
      have hm := lt_of_not_ge ((expNegInvGlue.zero_iff_nonpos).not.mp (hne (i, false)))
      change 0 < 1 + S * x i at hp
      change 0 < 1 + (-S) * x i at hm
      rw [abs_le]
      constructor
      · apply (mul_le_mul_iff_right₀ hS).mp
        nlinarith [mul_inv_cancel₀ hS.ne']
      · apply (mul_le_mul_iff_right₀ hS).mp
        nlinarith [mul_inv_cancel₀ hS.ne']
    have hsq : ‖x‖ ^ 2 ≤ (n : ℝ) * (S⁻¹) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _i : Fin n, (S⁻¹) ^ 2 := by
          apply sum_le_sum
          intro i hi
          nlinarith [sq_abs (x i), hcoord i, abs_nonneg (x i), inv_pos.mpr hS]
        _ = _ := by simp
    have hsmall : (n : ℝ) * (S⁻¹) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [inv_eq_one_div, div_pow, one_pow, ← mul_div_assoc, mul_one,
        div_le_iff₀ (sq_pos_of_pos hS)]
      dsimp [S]
      nlinarith [sq_nonneg (n : ℝ), (show (0 : ℝ) ≤ n by positivity)]
    have : ‖x‖ ≤ (1 / 4 : ℝ) := by nlinarith [norm_nonneg x]
    simpa only [mem_closedBall, dist_zero_right] using this
  · exact exists_gevreyTwo_prod_bound univ f (fun j _ => hf j)
      (fun j _ => exists_gevreyTwo_affine_glue_bound (L j) 1)

end RegularPointCoordinates

end

end OAI
