import OAI.Analysis.Cotype.DeletedTail
import OAI.Analysis.Cotype.ChebyshevTruncation

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
namespace Cotype

def chebBasis : Module.Basis ℕ ℝ ℝ[X] :=
  (chebyshevTsequence ℝ).basis (fun i =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((chebyshevTsequence ℝ).ne_zero i)))

@[simp] theorem chebBasis_apply (i : ℕ) : chebBasis i = T ℝ i := by
  simp [chebBasis, chebyshevTsequence]

def chebLow (d : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun Q := ∑ j ∈ Finset.range (d+1), (chebBasis.repr Q) j • T ℝ j
  map_add' Q R := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a Q := by simp [map_smul, mul_smul, Finset.smul_sum]

@[simp] theorem chebLow_basis (d j : ℕ) :
    chebLow d (T ℝ j) = if j ≤ d then T ℝ j else 0 := by
  change (∑ i ∈ Finset.range (d+1), (chebBasis.repr (T ℝ j)) i • T ℝ i) = _
  rw [← chebBasis_apply j, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem chebLow_degree (d : ℕ) (Q : ℝ[X]) : (chebLow d Q).degree ≤ d := by
  change (∑ j ∈ Finset.range (d+1), (chebBasis.repr Q) j • T ℝ j).degree ≤ d
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j hj
  apply (degree_smul_le _ _).trans
  have hd := (chebyshevTsequence ℝ).degree_eq j
  change (T ℝ j).degree = (j : WithBot ℕ) at hd
  rw [hd]
  exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)

theorem chebLow_eq_self {d : ℕ} {Q : ℝ[X]} (hQ : Q.degree ≤ d) : chebLow d Q = Q := by
  obtain ⟨c, rfl⟩ := exists_chebyshevExpansion Q d hQ
  simp only [chebyshevExpansion, map_sum, map_smul, chebLow_basis]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (Nat.le_of_lt_succ j.isLt)]

theorem chebLow_expansion {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ) :
    chebLow d (chebyshevExpansion c) = chebyshevTruncation c d := by
  simp only [chebyshevExpansion, map_sum, map_smul, chebLow_basis, chebyshevTruncation,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem chebLow_bound (Q : ℝ[X]) (d : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebLow d Q).eval x| ≤ 2*M*(d+1) := by
  obtain ⟨c, hc⟩ := exists_chebyshevExpansion Q Q.natDegree (degree_le_natDegree)
  rw [← hc, chebLow_expansion]
  exact chebyshevTruncation_bound c d hM (by simpa [hc] using hQ) hx

variable {m : ℕ}

def retainedCoefficient (f : SignMatrix m → ℝ) (d k l : ℕ) : ℝ :=
  if k ≤ d ∨ l ≤ d then Ckl f k l * (1/2 : ℝ)^(k*l) else 0

def retainedSectionS (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * u^l) • (X : ℝ[X])^k

def splitLowS (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) : ℝ[X] :=
  chebLow d (retainedSectionS f d u)

def splitHighU (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * (((X : ℝ[X])^k - chebLow d (X^k)).eval s)) • X^l

def retainedChebCoefficient (f : SignMatrix m → ℝ) (d j : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * (chebBasis.repr ((X : ℝ[X])^k)) j) • X^l

theorem retainedSectionS_eval (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    (retainedSectionS f d u).eval s = truncatedGrouped f d s u := by
  simp only [retainedSectionS, eval_finsetSum, eval_smul, smul_eq_mul, eval_pow,
    eval_X, truncatedGrouped]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  unfold retainedCoefficient
  split_ifs <;> ring

theorem retainedChebCoefficient_eval (f : SignMatrix m → ℝ) (d j : ℕ) (u : ℝ) :
    (retainedChebCoefficient f d j).eval u =
      (chebBasis.repr (retainedSectionS f d u)) j := by
  simp only [retainedChebCoefficient, retainedSectionS, eval_finsetSum, eval_smul,
    smul_eq_mul, eval_pow, eval_X, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem splitLowS_cheb (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    splitLowS f d u = ∑ j ∈ Finset.range (d+1),
      (retainedChebCoefficient f d j).eval u • T ℝ j := by
  simp only [splitLowS, chebLow, LinearMap.coe_mk, AddHom.coe_mk, retainedChebCoefficient_eval]

theorem bivariate_split_eval (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    truncatedGrouped f d s u = (splitLowS f d u).eval s + (splitHighU f d s).eval u := by
  rw [← retainedSectionS_eval f d s u]
  simp only [splitLowS, retainedSectionS, splitHighU, map_sum, map_smul,
    eval_finsetSum, eval_smul, smul_eq_mul, eval_sub, eval_pow, eval_X,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem splitLowS_degree (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    (splitLowS f d u).degree ≤ d := chebLow_degree d _

theorem splitHighU_degree (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (splitHighU f d s).degree ≤ d := by
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro l _
  by_cases hk : k ≤ d
  · have he : chebLow d ((X : ℝ[X])^k) = X^k := chebLow_eq_self (by simpa using hk)
    simp [he]
  · by_cases hl : l ≤ d
    · apply (degree_smul_le _ _).trans
      simpa using hl
    · simp [retainedCoefficient, hk, hl]

theorem splitLowS_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |(splitLowS f (degreeCutoff m) u).eval s| ≤ 4*M*(degreeCutoff m+1) := by
  have hh : ∀ x ∈ Set.Icc (-1) 1,
      |(retainedSectionS f (degreeCutoff m) u).eval x| ≤ 2*M := by
    intro x hx
    rw [retainedSectionS_eval]
    exact truncatedGrouped_bound ho hr hM hf hd hm (abs_le.mpr hx) hu
  have h := chebLow_bound (retainedSectionS f (degreeCutoff m) u) (degreeCutoff m)
    (by positivity : 0 ≤ 2*M) hh (abs_le.mp hs)
  dsimp [splitLowS]
  nlinarith

theorem splitHighU_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |(splitHighU f (degreeCutoff m) s).eval u| ≤ 6*M*(degreeCutoff m+1) := by
  have he := bivariate_split_eval f (degreeCutoff m) s u
  have h0 := truncatedGrouped_bound ho hr hM hf hd hm hs hu
  have h1 := splitLowS_bound ho hr hM hf hd hm hs hu
  have ha := abs_sub (truncatedGrouped f (degreeCutoff m) s u)
    ((splitLowS f (degreeCutoff m) u).eval s)
  rw [show truncatedGrouped f (degreeCutoff m) s u -
    (splitLowS f (degreeCutoff m) u).eval s = (splitHighU f (degreeCutoff m) s).eval u by linarith] at ha
  nlinarith [mul_nonneg hM (Nat.cast_nonneg (α := ℝ) (degreeCutoff m))]

end Cotype

end

end OAI
