import OAI.NumberTheory.JointDickman.Amplification.ThreeFormLocalBound
import OAI.NumberTheory.JointDickman.Amplification.CRTMean

namespace OAI

/-! # The three distinct residue roots in a graph representation -/

namespace JointDickman
open Finset

open Classical in
theorem sum_three_residueWeights {α : Type*} [Fintype α]
    (t u v : ℝ) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ x : α, residueWeight t a x * residueWeight u b x * residueWeight v c x =
      (Fintype.card α : ℝ) - 3 + t + u + v := by
  have he (x : α) :
      residueWeight t a x * residueWeight u b x * residueWeight v c x =
        1 + (if x = a then t-1 else 0) + (if x = b then u-1 else 0) +
          (if x = c then v-1 else 0) := by
    by_cases ha : x = a
    · subst x
      simp [residueWeight, hab, hac]
    · by_cases hb : x = b
      · subst x
        simp [residueWeight, Ne.symm hab, hbc]
      · by_cases hc : x = c
        · subst x
          simp [residueWeight, Ne.symm hac, Ne.symm hbc]
        · simp [residueWeight, ha, hb, hc]
  simp_rw [he]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    sum_ite_eq', mem_univ, ite_true]
  ring

theorem graph_three_root_mean {p : ℕ} [NeZero p] (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ x : ZMod p, residueWeight (1/2) a x * residueWeight (1/2) b x *
      residueWeight (1/2) c x) / (p : ℝ) = 1 - 3/(2*(p : ℝ)) := by
  rw [sum_three_residueWeights _ _ _ a b c hab hac hbc, ZMod.card]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

/-- Product residue tests factor exactly, including nonnormalized tests. -/
theorem crt_product_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) /
      (∏ i, (m i : ℝ)) = ∏ i, (∑ x : ZMod (m i), f i x) / (m i : ℝ) := by
  rw [crt_period_sum m (fun i => NeZero.pos (m i)) hcop f, prod_div_distrib]

/-- At good primes the three graph roots are `0`, `-j`, and `b/c`. -/
theorem graph_roots_distinct {p : ℕ} [Fact p.Prime]
    (a b c j : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hj : j ≠ 0) (he : a = b+j*c) :
    (0 : ZMod p) ≠ -j ∧ (0 : ZMod p) ≠ b/c ∧ -j ≠ b/c := by
  refine ⟨by simpa using hj, Ne.symm (div_ne_zero hb hc), ?_⟩
  intro h
  have hmul : -j*c = b := (eq_div_iff hc).mp h
  apply ha
  rw [he, ← hmul]
  ring

end JointDickman

end OAI
