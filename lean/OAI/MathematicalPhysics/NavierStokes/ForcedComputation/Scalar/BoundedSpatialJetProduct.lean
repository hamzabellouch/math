import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-! Bounded spatial jets of pointwise bilinear products.

The finite-order Leibniz estimate gives the constant `2^k`. In particular,
fixing a smooth bounded coefficient gives a bounded linear multiplication
operator on the jet Banach space used in a Volterra equation.
-/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bundle the actual derivatives of a function with bounded jets. -/
def ofFunctionFamily (k : ℕ) (f : E → F) (hf : ContDiff ℝ k f) (C : ℝ)
    (hC : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : Family E F k :=
  fun i => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (show Value E F i.val from iteratedFDeriv ℝ i.val f x))
    (by
      change Continuous (iteratedFDeriv ℝ i.val f)
      exact hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ i.isLt))
    C (hC i.val (Nat.le_of_lt_succ i.isLt))

/-- A `C^k` function whose first `k` derivatives are uniformly bounded defines a jet. -/
def ofFunction (k : ℕ) (f : E → F) (hf : ContDiff ℝ k f) (C : ℝ)
    (hC : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : Space E F k := by
  refine ⟨ofFunctionFamily E F k f hf C hC, ?_⟩
  apply (mem_compatible E F k _).mpr
  intro i x
  have hd := (hf.differentiable_iteratedFDeriv (m := i.val)
    (by exact_mod_cast i.isLt) x).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at hd
  convert! hd using 1

@[simp] theorem ofFunction_apply (k : ℕ) (f : E → F) (hf : ContDiff ℝ k f) (C : ℝ)
    (hC : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (i : Fin (k + 1)) (x : E) :
    (ofFunction E F k f hf C hC).val i x =
      (show Value E F i.val from iteratedFDeriv ℝ i.val f x) := rfl

@[simp] theorem function_ofFunction (k : ℕ) (f : E → F) (hf : ContDiff ℝ k f) (C : ℝ)
    (hC : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    function E F k (ofFunction E F k f hf C hC) x = f x := by
  rw [function_apply, ofFunction_apply]
  change (continuousMultilinearCurryFin0 ℝ E F) (iteratedFDeriv ℝ 0 f x) = f x
  rw [iteratedFDeriv_zero_eq_comp]
  exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply (f x)

theorem norm_ofFunction_le (k : ℕ) (f : E → F) (hf : ContDiff ℝ k f) (C : ℝ)
    (hC : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hC₀ : 0 ≤ C) :
    ‖ofFunction E F k f hf C hC‖ ≤ C := by
  change ‖ofFunctionFamily E F k f hf C hC‖ ≤ C
  apply (pi_norm_le_iff_of_nonneg hC₀).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le hC₀).mpr
  exact hC i.val (Nat.le_of_lt_succ i.isLt)

/-- A compatible family is determined by its zeroth-order function. -/
theorem function_injective (k : ℕ) : Function.Injective (function E F k) := by
  intro J K h
  apply Subtype.ext
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  have hf : (function E F k J : E → F) = function E F k K := congrArg DFunLike.coe h
  have hd := congrArg (fun f : E → F => iteratedFDeriv ℝ i.val f x) hf
  rw [iteratedFDeriv_function E F k J i.val (Nat.le_of_lt_succ i.isLt),
    iteratedFDeriv_function E F k K i.val (Nat.le_of_lt_succ i.isLt)] at hd
  exact hd

variable (G H : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The finite Leibniz estimate, uniformly in the spatial point. -/
theorem bilinear_derivative_bound (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) (n : ℕ) (hn : n ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B (function E F k J y) (function E G k K y)) x‖ ≤
      ‖B‖ * (2 : ℝ) ^ k * ‖J‖ * ‖K‖ := by
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (function E F k J) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (function E G k K) x‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear (function_contDiff E F k J)
        (function_contDiff E G k K) x (by exact_mod_cast hn)
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖J‖ * ‖K‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le E F k J i hi' x)
          (Nat.cast_nonneg _)
      · exact norm_iteratedFDeriv_le E G k K (n - i) ((Nat.sub_le n i).trans hn) x
      · exact norm_nonneg _
      · positivity
    _ = ‖B‖ * (2 : ℝ) ^ n * ‖J‖ * ‖K‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      ring
    _ ≤ ‖B‖ * (2 : ℝ) ^ k * ‖J‖ * ‖K‖ := by
      have hp : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (norm_nonneg B)) (norm_nonneg J)) (norm_nonneg K)

/-- Pointwise application of a bounded bilinear map to two compatible jets. -/
def bilinear (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) : Space E H k :=
  ofFunction E H k (fun y => B (function E F k J y) (function E G k K y))
    ((B.contDiff.comp (function_contDiff E F k J)).clm_apply (function_contDiff E G k K))
    (‖B‖ * (2 : ℝ) ^ k * ‖J‖ * ‖K‖)
    (bilinear_derivative_bound E F G H k B J K)

@[simp] theorem function_bilinear (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) (x : E) :
    function E H k (bilinear E F G H k B J K) x =
      B (function E F k J x) (function E G k K x) :=
  function_ofFunction E H k _ _ _ _ x

theorem norm_bilinear_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) :
    ‖bilinear E F G H k B J K‖ ≤ ‖B‖ * (2 : ℝ) ^ k * ‖J‖ * ‖K‖ :=
  norm_ofFunction_le E H k _ _ _ _ (by positivity)

end ForcedComputation.BoundedSpatialJets

end

end OAI
