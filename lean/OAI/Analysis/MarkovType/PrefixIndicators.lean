import OAI.Analysis.MarkovType.OrderedSequences
import OAI.Analysis.MarkovType.FiniteCharts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

@[simp] theorem prefixCut_add (x y : C00) (k : ℕ) :
    prefixCut (x + y) k = prefixCut x k + prefixCut y k := by
  simp only [prefixCut, Finsupp.add_apply, Finset.sum_add_distrib]

@[simp] theorem prefixCut_sub (x y : C00) (k : ℕ) :
    prefixCut (x - y) k = prefixCut x k - prefixCut y k := by
  simp only [prefixCut, Finsupp.sub_apply, Finset.sum_sub_distrib]

@[simp] theorem prefixCut_neg (x : C00) (k : ℕ) :
    prefixCut (-x) k = -prefixCut x k := by
  simp only [prefixCut, Finsupp.neg_apply, Finset.sum_neg_distrib]

@[simp] theorem prefixCut_smul (r : ℝ) (x : C00) (k : ℕ) :
    prefixCut (r • x) k = r * prefixCut x k := by
  simp only [prefixCut, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem prefixCut_finset_sum {ι : Type*} (s : Finset ι) (x : ι → C00) (k : ℕ) :
    prefixCut (∑ i ∈ s, x i) k = ∑ i ∈ s, prefixCut (x i) k := by
  simp only [prefixCut, Finsupp.finsetSum_apply]
  exact Finset.sum_comm

@[simp] theorem prefixCut_basis (i k : ℕ) :
    prefixCut (C00.basis i) k = if i < k then (1 : ℝ) else 0 := by
  classical
  simp [prefixCut, C00.basis, Finsupp.single_apply, Finset.mem_range]

namespace PrefixIndicators

def halfOpen (a b y : ℝ) : ℝ := if a ≤ y ∧ y < b then 1 else 0

def periodic (a b y : ℝ) : ℝ := by
  classical
  exact if ∃ j : ℤ, a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ) then 1 else 0

theorem le_indicator_sub (a b y : ℝ) (hab : a < b) :
    (if a ≤ y then (1 : ℝ) else 0) - (if b ≤ y then 1 else 0) =
      halfOpen a b y := by
  unfold halfOpen
  by_cases ha : a ≤ y
  · by_cases hb : b ≤ y
    · simp [ha, hb, not_lt_of_ge hb]
    · simp [ha, hb, lt_of_not_ge hb]
  · have hb : ¬ b ≤ y := fun h => ha (hab.le.trans h)
    simp [ha, hb]

theorem translate_unique {a b y : ℝ} (ha : 0 < a) (hb : b < 1)
    {i j : ℤ} (hi : a + (i : ℝ) ≤ y ∧ y < b + (i : ℝ))
    (hj : a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ)) : i = j := by
  have hnot (u v : ℤ)
      (hu : a + (u : ℝ) ≤ y ∧ y < b + (u : ℝ))
      (hv : a + (v : ℝ) ≤ y ∧ y < b + (v : ℝ)) : ¬ u < v := by
    intro huv
    have hstep : u + 1 ≤ v := by omega
    have hstepR : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hstep
    linarith [hu.2, hv.1]
  exact le_antisymm (le_of_not_gt (hnot j i hj hi))
    (le_of_not_gt (hnot i j hi hj))

theorem sum_halfOpen_eq_periodic {a b y : ℝ} (ha : 0 < a) (hb : b < 1)
    (L : ℕ) (hy0 : 0 < y) (hyL : y < (L : ℝ)) :
    (∑ j : Fin L, halfOpen (a + (j.val : ℝ)) (b + (j.val : ℝ)) y) =
      periodic a b y := by
  classical
  unfold periodic
  by_cases hex : ∃ j : ℤ, a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ)
  · rw [ite_eq_left hex]
    obtain ⟨j, hj⟩ := hex
    have hj0 : 0 ≤ j := by
      by_contra h
      have hjneg : j ≤ -1 := by omega
      have hjnegR : (j : ℝ) ≤ -1 := by exact_mod_cast hjneg
      linarith [hj.2]
    have hjL : j < (L : ℤ) := by
      by_contra h
      have hjge : (L : ℤ) ≤ j := le_of_not_gt h
      have hjgeR : (L : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjge
      linarith [hj.1]
    have hjcast : (j.toNat : ℤ) = j := by omega
    have hjnat : j.toNat < L := by omega
    let k : Fin L := ⟨j.toNat, hjnat⟩
    have hkR : (k.val : ℝ) = (j : ℝ) := by
      dsimp only [k]
      exact_mod_cast hjcast
    have hk : a + (k.val : ℝ) ≤ y ∧ y < b + (k.val : ℝ) := by
      simpa only [hkR] using hj
    rw [Finset.sum_eq_single k]
    · simp only [halfOpen, ite_eq_left hk]
    · intro i _ hik
      unfold halfOpen
      apply ite_eq_right
      intro hi
      have heq : (i.val : ℤ) = (k.val : ℤ) :=
        translate_unique ha hb (by simpa only [Int.cast_natCast] using hi)
          (by simpa only [Int.cast_natCast] using hk)
      apply hik
      apply Fin.ext
      exact_mod_cast heq
    · simp
  · rw [ite_eq_right hex]
    apply Finset.sum_eq_zero
    intro i _
    unfold halfOpen
    apply ite_eq_right
    intro hi
    apply hex
    exact ⟨(i.val : ℤ), by simpa only [Int.cast_natCast] using hi⟩

end PrefixIndicators

theorem prefixCut_chart_basis_sub {Λ : Finset ℝ} {B : ℕ}
    (C : Chart Λ B) (a b y : ↥Λ) (hab : (a : ℝ) < b) :
    prefixCut (C00.basis (C a).val - C00.basis (C b).val) ((C y).val + 1) =
      PrefixIndicators.halfOpen a b y := by
  have hle (x : ↥Λ) : (C x).val < (C y).val + 1 ↔ (x : ℝ) ≤ y := by
    rw [Nat.lt_succ_iff]
    exact C.le_iff_le
  simp only [prefixCut_sub, prefixCut_basis, hle a, hle b]
  exact PrefixIndicators.le_indicator_sub a b y hab

end MarkovSuperreflexivity

end

end OAI
