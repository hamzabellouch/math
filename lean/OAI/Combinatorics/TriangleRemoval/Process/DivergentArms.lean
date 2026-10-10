import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.PairVisitProbability
import OAI.Combinatorics.TriangleRemoval.Probability.RootPathVisitProbability
import OAI.Combinatorics.TriangleRemoval.Probability.RootPairVisitProbability2

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma factorial_weight_add_le {x : ℝ} (hx : 0 ≤ x) (i j : ℕ) :
    x^(i+j)/(Nat.factorial (i+j) : ℝ) ≤
      (x^i/(i.factorial : ℝ))*(x^j/(j.factorial : ℝ)) := by
  have hf : (i.factorial : ℝ)*(j.factorial : ℝ) ≤ ((i+j).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (i+j))
      (Nat.factorial_mul_factorial_dvd_factorial_add i j)
  rw [pow_add,div_mul_div_comm]
  exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hx _) (pow_nonneg hx _))
    (mul_pos (by positivity) (by positivity)) hf

lemma cube_ge_self {C : ℝ} (hC : 1 ≤ C) : C ≤ C^3 := by nlinarith [sq_nonneg (C-1)]
lemma cube_ge_sq {C : ℝ} (hC : 1 ≤ C) : C^2 ≤ C^3 := by
  have h := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
  nlinarith

def DivergentArms {A : Type*} (p q : List A) : Prop :=
  match p,q with
  | a :: _, b :: _ => a ≠ b
  | _,_ => True

section ActualPairFactorial
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma actualPairVisitProbability_le_left (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      actualPathVisitProbability H N d k focus parent p := by
  unfold actualPairVisitProbability actualPathVisitProbability
  apply pmf_boolean_map_le
  intro z _ h
  exact (Bool.and_eq_true_iff.mp h).1

lemma actualPairVisitProbability_le_right (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      actualPathVisitProbability H N d k focus parent q := by
  unfold actualPairVisitProbability actualPathVisitProbability
  apply pmf_boolean_map_le
  intro z _ h
  exact (Bool.and_eq_true_iff.mp h).2

theorem actualPairVisitProbability_pattern_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine left right : List (ι × τ)) (hdiv : DivergentArms left right)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (ha : LegalQueryPath H focus parent (spine ++ left))
    (hb' : LegalQueryPath H focus parent (spine ++ right))
    (halen : (spine ++ left).length ≤ d) (hblen : (spine ++ right).length ≤ d) :
    actualPairVisitProbability H N d k focus parent (spine ++ left) (spine ++ right) ≤
      C^3 * (prefixWeight (fun t => (2/(N : ℝ))*b t) k ^
        (spine.length+left.length+right.length) /
        ((spine.length.factorial : ℝ)*(left.length.factorial : ℝ)*(right.length.factorial : ℝ))) := by
  let w := fun t => (2/(N : ℝ))*b t
  let x := prefixWeight w k
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (by positivity) (hb t)
  have hx : 0 ≤ x := prefixWeight_nonneg hw k
  have hc0 : 0 ≤ C := by linarith
  have hc3 : 0 ≤ C^3 := pow_nonneg hc0 _
  cases left with
  | nil =>
    have ht := (actualPairVisitProbability_le_right H N d k focus parent (spine ++ []) (spine ++ right)).trans
      (actualRootPathVisitProbability_factorial H N b hb hq C hC hlower (spine ++ right)
        d k hkd hkN hblen focus parent hb')
    have hsplit := factorial_weight_add_le hx spine.length right.length
    have hg := mul_le_mul_of_nonneg_left hsplit hc3
    have hf : C*(x^(spine.length+right.length)/((spine.length+right.length).factorial : ℝ)) ≤
        C^3*(x^(spine.length+right.length)/((spine.length+right.length).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (cube_ge_self hC) (by positivity)
    apply ht.trans
    change C*(x^((spine ++ right).length)/(((spine ++ right).length).factorial : ℝ)) ≤ _
    simp only [List.length_append,List.length_nil,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
    apply hf.trans
    simpa only [div_mul_div_comm,← pow_add] using hg
  | cons a as =>
    cases right with
    | nil =>
      have ht := (actualPairVisitProbability_le_left H N d k focus parent (spine ++ a :: as) (spine ++ [])).trans
        (actualRootPathVisitProbability_factorial H N b hb hq C hC hlower (spine ++ a :: as)
          d k hkd hkN halen focus parent ha)
      have hsplit := factorial_weight_add_le hx spine.length (a :: as).length
      have hg := mul_le_mul_of_nonneg_left hsplit hc3
      have hf : C*(x^(spine.length+(a :: as).length)/((spine.length+(a :: as).length).factorial : ℝ)) ≤
          C^3*(x^(spine.length+(a :: as).length)/((spine.length+(a :: as).length).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (cube_ge_self hC) (by positivity)
      apply ht.trans
      change C*(x^((spine ++ a :: as).length)/(((spine ++ a :: as).length).factorial : ℝ)) ≤ _
      simp only [List.length_append,List.length_nil,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      apply hf.trans
      simpa only [div_mul_div_comm,← pow_add] using hg
    | cons a' as' =>
      have ht := (actualPairVisitProbability_le_marked H N d k focus parent _ _).trans
        (rootPairVisitProbability_spine H N b hb hq C hc0 hlower spine a a' hdiv as as'
          d k hkd hkN focus parent ha hb'
          (by simpa only [List.length_append,List.length_cons] using halen)
          (by simpa only [List.length_append,List.length_cons] using hblen))
      have hs := three_segment_weight_le hw spine.length (as.length+1) (as'.length+1) k
      have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
      have he : C^2 * orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
          orderedWeight w (as'.length+1) k =
          C^2*(orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
            orderedWeight w (as'.length+1) k) := by ring
      apply ht.trans
      change C^2 * orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
        orderedWeight w (as'.length+1) k ≤ _
      rw [he]
      apply hp.trans
      apply mul_le_mul_of_nonneg_right (cube_ge_sq hC)
      exact div_nonneg (pow_nonneg (prefixWeight_nonneg hw k) _) (by positivity)

end ActualPairFactorial
end SharpTerminalLeave

end

end OAI
