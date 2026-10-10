import Mathlib
import OAI.Combinatorics.UniformKServer.RankTracking
import OAI.Combinatorics.UniformKServer.RankFunctions

namespace OAI

                               
section

/-! Exact size rank and held core flags from companion §03. -/
noncomputable section
namespace UniformKServer.RankData
open RankFunctions

def sizeRank (p : ℝ) : ℝ := (max (3/4-p) 0)^2 / (3/4)^2

theorem sizeRank_nonneg (p : ℝ) : 0 ≤ sizeRank p := by
  unfold sizeRank
  positivity

theorem sizeRank_zero : sizeRank 0 = 1 := by norm_num [sizeRank]
theorem sizeRank_one : sizeRank 1 = 0 := by norm_num [sizeRank]

theorem sizeRank_convex : ConvexOn ℝ Set.univ sizeRank := by
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ => 3/4-p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have hm := hlin.sup (convexOn_const 0 convex_univ)
  have hh := (hm.pow (fun p _ => le_max_right (3/4-p) 0) 2).smul
    (show (0 : ℝ) ≤ ((3/4)^2)⁻¹ by norm_num)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa [sizeRank, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.2 hx hy ha hb hab

theorem sizeRank_sqrt (p : ℝ) : Real.sqrt (sizeRank p) = max (3/4-p) 0 / (3/4) := by
  rw [sizeRank, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (le_max_right _ _)]
  norm_num

theorem sizeRank_sqrt_lipschitz (p q : ℝ) :
    |Real.sqrt (sizeRank p)-Real.sqrt (sizeRank q)| ≤ (4/3)*|p-q| := by
  rw [sizeRank_sqrt, sizeRank_sqrt, ← sub_div, abs_div]
  have hm := abs_max_sub_max_le_max (3/4-p) (0 : ℝ) (3/4-q) 0
  have he : |(3/4-p)-(3/4-q)| = |p-q| := by
    rw [show (3/4-p)-(3/4-q) = -(p-q) by ring, abs_neg]
  rw [he, sub_self, abs_zero, max_eq_left (abs_nonneg (p-q))] at hm
  norm_num
  nlinarith

theorem sizeRank_le_complement {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    sizeRank p ≤ 1-p := by
  by_cases h : p ≤ 3/4
  · rw [sizeRank, max_eq_left (sub_nonneg.mpr h)]
    norm_num
    nlinarith [mul_nonneg hp.1 (show 3/4-p ≥ 0 by linarith)]
  · rw [sizeRank, max_eq_right (by linarith : 3/4-p ≤ 0)]
    norm_num
    exact hp.2

theorem sizeRank_at_cutoff {p : ℝ} (hp : p ≤ sstar) :
    1/36 ≤ sizeRank p := by
  have hp' : p ≤ 5/8 := hp
  have hm : max (3/4-p) 0 = 3/4-p := max_eq_left (by linarith)
  rw [sizeRank, hm]
  norm_num
  nlinarith [sq_nonneg (5/8-p)]

variable {Ω : Type*} [Fintype Ω]
def core (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω) : Bool :=
  decide (RankTracking.absoluteReference I (pstar/8) t ω ≤ pstar/2)

theorem core_small (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (h : core I t ω = true) : I.posterior t ω ≤ 5*pstar/8 := by
  have hr : RankTracking.absoluteReference I (pstar/8) t ω ≤ pstar/2 := by
    simpa only [core, decide_eq_true_eq] using h
  have he := (abs_le.mp (RankTracking.absoluteReference_spec I (pstar/8)
    (by norm_num [pstar]) t ω)).2
  linarith

theorem noncore_large (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (h : core I t ω = false) : 3*pstar/8 < I.posterior t ω := by
  have hr : pstar/2 < RankTracking.absoluteReference I (pstar/8) t ω := by
    simpa only [core, decide_eq_false_iff_not, not_le] using h
  have he := (abs_le.mp (RankTracking.absoluteReference_spec I (pstar/8)
    (by norm_num [pstar]) t ω)).1
  linarith

theorem small_core (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (h : I.posterior t ω < pstar/4) : core I t ω = true := by
  cases hc : core I t ω with
  | true => rfl
  | false =>
    have := noncore_large I t ω hc
    norm_num [pstar] at *
    linarith

theorem core_refresh (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    (if core I (t+1) ω = core I t ω then (0 : ℝ) else 1) ≤
      (if RankTracking.absoluteReference I (pstar/8) (t+1) ω =
        RankTracking.absoluteReference I (pstar/8) t ω then (0 : ℝ) else 1) := by
  split_ifs with hc hr hr
  · rfl
  · norm_num
  · exact (hc (by simp only [core, hr])).elim
  · rfl

variable {A : Type*} [Fintype A]
def coreCount (c : A → Bool) : ℝ := ∑ a, if c a then 1 else 0
def coreMass (c : A → Bool) (p : A → ℝ) : ℝ := ∑ a, if c a then p a else 0
def flex (c : A → Bool) (β : ℝ) (p : A → ℝ) : ℝ :=
  ∑ a, if c a then 0 else rank β (p a)
def totalRank (β : ℝ) (p : A → ℝ) : ℝ := ∑ a, rank β (p a)
def totalSize (p : A → ℝ) : ℝ := ∑ a, sizeRank (p a)

theorem core_mass_bounds (c : A → Bool) (p : A → ℝ)
    (hp : ∀ a, p a ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ coreMass c p ∧ coreMass c p ≤ coreCount c := by
  constructor
  · exact Finset.sum_nonneg fun a _ => by split <;> simp_all
  · apply Finset.sum_le_sum
    intro a ha
    split <;> simp_all

theorem core_decomposition (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hc : ∀ a, c a = true → p a ≤ pstar) :
    totalRank β p = coreCount c - β * coreMass c p + flex c β p := by
  unfold totalRank coreCount coreMass flex
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  cases he : c a with
  | true => simp [rank, hc a he]
  | false => simp

theorem rank_size_domination {β p : ℝ} (hβ : allowed β) (hp : 0 ≤ p) :
    rank β p ≤ 36 * sizeRank p := by
  by_cases hs : sstar ≤ p
  · rw [rank_beyond hs]
    exact mul_nonneg (by norm_num) (sizeRank_nonneg p)
  · have := sizeRank_at_cutoff (le_of_not_ge hs)
    linarith [rank_le_one hβ hp]

theorem core_flex_domination (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hβ : allowed β) (hp : ∀ a, 0 ≤ p a)
    (hc : ∀ a, c a = true → p a ≤ pstar) :
    coreCount c + flex c β p ≤ 36 * totalSize p := by
  unfold coreCount flex totalSize
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  cases he : c a with
  | false => simpa [he] using rank_size_domination hβ (hp a)
  | true =>
    have hs : p a ≤ sstar := by
      have := hc a he
      norm_num [pstar, sstar] at *
      linarith
    have := sizeRank_at_cutoff hs
    simp only [↓reduceIte, add_zero]
    linarith

theorem inactive_ranks (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hc : ∀ a, c a = true → p a ≤ pstar)
    (hm : totalSize p ≤ 10*(10:ℝ)^(-4:ℤ)) :
    coreCount c = 0 ∧ totalRank β p = 0 ∧ flex c β p = 0 := by
  have hlarge (a : A) : sstar < p a := by
    by_contra h
    have hsz := sizeRank_at_cutoff (le_of_not_gt h)
    have hle : sizeRank (p a) ≤ totalSize p :=
      Finset.single_le_sum (fun b _ => sizeRank_nonneg (p b)) (Finset.mem_univ a)
    norm_num at hm
    linarith
  have hzero (a : A) : rank β (p a) = 0 := rank_beyond (hlarge a).le
  have hfalse (a : A) : c a = false := by
    cases he : c a with
    | false => rfl
    | true =>
      have := hc a he
      have := hlarge a
      norm_num [pstar, sstar] at *
      linarith
  simp [coreCount, totalRank, flex, hfalse, hzero]

end UniformKServer.RankData

end


end

end OAI
