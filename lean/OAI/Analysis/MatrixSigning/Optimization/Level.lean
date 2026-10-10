import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SearchStep
import OAI.Analysis.MatrixSigning.Optimization.BlockScalar

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def level (δ U : ℚ) (k : ℕ) : ℚ := -U+k*δ

def Pencil.levelCandidate (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ) (k : ℕ) :
    Fin n → ℚ := (B.withLevel f (level δ U k)).search r R 0

def Pencil.optimize (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ) : ℕ → Fin n → ℚ
  | 0 => B.levelCandidate f δ r R U 0
  | k+1 =>
      let y := B.optimize f δ r R U k
      if (B.withLevel f (level δ U k)).witness y = none then y
      else B.levelCandidate f δ r R U (k+1)

lemma Pencil.witness_withLevel (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) (y : Fin n → ℚ) :
    (B.withLevel f q).witness y = none ↔
      realVector y ∈ B.feasible ∧ (fun i => (f i:ℝ)) ⬝ᵥ realVector y ≤ (q:ℝ) := by
  rw [Pencil.witness_none_iff]
  change realVector y ∈ (B.withLevel f q).feasible ↔ _
  exact B.withLevel_feasible f q (realVector y)

lemma level_mono {δ U : ℚ} (hδ : 0 ≤ δ) : Monotone (level δ U) := by
  intro k l hkl
  unfold level
  exact add_le_add (le_refl (-U)) (mul_le_mul_of_nonneg_right (show (k:ℚ) ≤ (l:ℚ) by exact_mod_cast hkl) hδ)

lemma Pencil.optimize_preserves (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) {k l : ℕ} (hkl : k ≤ l)
    (hk : (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none) :
    B.optimize f δ r R U l = B.optimize f δ r R U k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hl : (B.withLevel f (level δ U l)).witness (B.optimize f δ r R U l)=none := by
      rw [ih,B.witness_withLevel]
      obtain ⟨hm,ho⟩ := (B.witness_withLevel _ _ _).mp hk
      refine ⟨hm,ho.trans ?_⟩
      exact_mod_cast level_mono hδ hkl
    rw [Pencil.optimize,ite_eq_left hl,ih]

lemma Pencil.optimize_accepts (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) (k : ℕ)
    (hk : (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none) :
    (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none := by
  cases k with
  | zero => exact hk
  | succ k =>
    by_cases h : (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none
    · simp only [Pencil.optimize,h,ite_true]
      rw [B.witness_withLevel] at h ⊢
      refine ⟨h.1,h.2.trans ?_⟩
      exact_mod_cast level_mono hδ (Nat.le_succ k)
    · simpa only [Pencil.optimize,h,ite_false] using hk

theorem Pencil.optimize_bound (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) {k K : ℕ} (hkK : k ≤ K)
    (hk : (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none) :
    realVector (B.optimize f δ r R U K) ∈ B.feasible ∧
      (fun i => (f i:ℝ)) ⬝ᵥ realVector (B.optimize f δ r R U K) ≤ (level δ U k:ℝ) := by
  have ha := B.optimize_accepts f δ r R U hδ k hk
  rw [B.optimize_preserves f δ r R U hδ hkK ha]
  exact (B.witness_withLevel _ _ _).mp ha

lemma Pencil.levelCandidate_accepts (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R)
    (hc : ‖c‖ ≤ (R:ℝ))
    (hball : Metric.closedBall c (r:ℝ) ⊆
      B.feasible ∩ {y | (fun i => (f i:ℝ)) ⬝ᵥ y ≤ (level δ U k:ℝ)}) :
    (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none := by
  apply Pencil.search_accepts _ _ _ _ c hr hr1 hR
  · intro y hy
    exact (B.withLevel_feasible f _ y).mpr (hball hy)
  · have hz : realVector (0 : Fin n → ℚ)=0 := by ext i; simp [realVector]
    simpa only [hz,zero_sub,norm_neg] using hc

end CurrentKS.RationalSDP

end OAI
