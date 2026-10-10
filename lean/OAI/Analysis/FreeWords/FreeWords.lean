import Mathlib
import OAI.Analysis.FreeWords.GNSCutNorms
import OAI.Analysis.FreeWords.GNSProjectionRemainder
import OAI.Analysis.FreeWords.NumericCuts

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

def freeWordsError (r : ℕ) : ℝ :=
  (2*r+1)*r.factorial+(r.factorial:ℝ)*2^r*(3*r+1)

theorem freeWordsError_nonneg (r : ℕ) : 0 ≤ freeWordsError r := by
  unfold freeWordsError
  positivity

theorem decay_pow (d m : ℕ) : decay d^m = (d:ℝ)^(-(m:ℝ)/2) := by
  rw [decay, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (inv_nonneg.mpr (Nat.cast_nonneg d)), Real.inv_rpow (Nat.cast_nonneg d),
    ← Real.rpow_neg (Nat.cast_nonneg d)]
  congr 1
  ring

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

namespace FreePartitions

variable (P : FreePartitions τ r d)

theorem centeredSum_bound (hτ : FaithfulTracial τ) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (W : Multiset (Fin d)) :
    ‖P.centeredSum W‖ ≤ 5*Real.sqrt ((r-1).factorial:ℝ)*decay d^(r-1) +
      (2*r+1:ℝ)*r.factorial*decay d^r := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have h := P.centeredSum_cut_bound hτ (by omega) W
  have hnum := sum_cuts_numeric m (decay_nonneg d) (decay_le_one hd)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h.trans hnum

theorem forwardSum_bound (hτ : FaithfulTracial τ) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (W : Multiset (Fin d)) :
    ‖P.forwardSum W‖ ≤ 5*Real.sqrt ((r-1).factorial:ℝ)*decay d^(r-1) +
      freeWordsError r*decay d^r := by
  have hc := P.centeredSum_bound hτ hr hd W
  have hrem := P.forwardSum_remainder hτ hd W
  have ht := norm_add_le (P.centeredSum W) (P.forwardSum W-P.centeredSum W)
  rw [add_sub_cancel] at ht
  unfold freeWordsError
  nlinarith

omit [StarOrderedRing A] in
theorem wordSum_eq_star_forwardSum (W : Sym (Fin d) r) :
    wordSum P W = star (P.forwardSum (W:Multiset (Fin d))) := by
  classical
  have hstar (l : List A) (hl : ∀ x ∈ l, star x = x) : star l.prod = l.reverse.prod := by
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.prod_cons, star_mul, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [hl x List.mem_cons_self, ih (fun y hy => hl y (List.mem_cons_of_mem x hy))]
  simp only [wordSum, forwardSum, Finset.sum_filter, star_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [tupleLabels]
  split_ifs with h
  · simp only [h, ite_true]
    exact (hstar _ (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact P.selfadjoint j (a j))).symm
  · simp only [h, ite_false, star_zero]

theorem wordSum_bound (hτ : FaithfulTracial τ) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (W : Sym (Fin d) r) :
    ‖wordSum P W‖ ≤ 5*Real.sqrt ((r-1).factorial:ℝ)*decay d^(r-1) +
      freeWordsError r*decay d^r := by
  rw [P.wordSum_eq_star_forwardSum]
  exact (norm_star _).le.trans (P.forwardSum_bound hτ hr hd _)

end FreePartitions

theorem free_projection_words (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, r ≤ d₀ ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ (A : Type*) [CStarAlgebra A] [PartialOrder A]
        [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ), FaithfulTracial τ →
        ∀ (P : FreePartitions τ r d) (W : Sym (Fin d) r),
          ‖wordSum P W‖ ≤
            (if (W : Multiset (Fin d)).Nodup then
              7 * Real.sqrt ((r - 1).factorial : ℝ) else C) *
              (d : ℝ) ^ (-((r - 1 : ℕ) : ℝ) / 2) := by
  let K := freeWordsError r
  have hK : 0 ≤ K := freeWordsError_nonneg r
  have hS : 1 ≤ Real.sqrt ((r-1).factorial:ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast Nat.factorial_pos (r-1))
  obtain ⟨n, hn⟩ := exists_nat_ge (K^2)
  refine ⟨7*Real.sqrt ((r-1).factorial:ℝ), by nlinarith, max r n, le_max_left _ _, ?_⟩
  intro d hd A instA instO instS τ hτ P W
  have hd1 : 1 ≤ d := hr.trans ((le_max_left r n).trans hd)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
  have hKd : K^2 ≤ (d:ℝ) := hn.trans (by exact_mod_cast (le_max_right r n).trans hd)
  have hKs : (K*decay d)^2 ≤ 1 := by
    rw [mul_pow, decay_sq]
    exact (mul_inv_le_iff₀ hd0).mpr (by simpa using hKd)
  have hKt : K*decay d ≤ 1 := (sq_le_sq₀ (mul_nonneg hK (decay_nonneg d)) zero_le_one).mp
    (by simpa using hKs)
  have hp : decay d^r = decay d^(r-1)*decay d := by
    conv_lhs => rw [show r=(r-1)+1 by omega]
    rw [pow_succ]
  have hb := P.wordSum_bound hτ hr hd1 W
  rw [hp] at hb
  simp only [ite_self]
  rw [← decay_pow]
  apply hb.trans
  change 5*Real.sqrt ((r-1).factorial:ℝ)*decay d^(r-1) + K*(decay d^(r-1)*decay d) ≤ _
  calc
    _ = (5*Real.sqrt ((r-1).factorial:ℝ)+K*decay d)*decay d^(r-1) := by ring
    _ ≤ (7*Real.sqrt ((r-1).factorial:ℝ))*decay d^(r-1) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg (decay_nonneg d) _)

end

end KKFreeWords
end

end OAI
