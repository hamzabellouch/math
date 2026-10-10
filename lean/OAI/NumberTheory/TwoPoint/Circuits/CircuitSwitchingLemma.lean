import OAI.NumberTheory.TwoPoint.Circuits.CircuitSwitchingMass
import OAI.NumberTheory.TwoPoint.Circuits.CircuitTreeWalk
import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateApproximation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A switching estimate sufficient for the fixed-depth application. The
position/separator encoding gives a quadratic dependence on term width;
this still yields polylogarithmic degree for every fixed circuit depth. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finite_geometric_tail (n s : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (∑ i : Fin (n + 1), if s ≤ i.val then q ^ i.val else 0) ≤ 2 * q ^ s := by
  let I := (univ : Finset (Fin (n + 1))).filter (fun i => s ≤ i.val)
  have hs : (∑ i : Fin (n + 1), if s ≤ i.val then q ^ i.val else 0) =
      ∑ i ∈ I, q ^ i.val := (sum_filter _ _).symm
  rw [hs]
  calc
    _ ≤ ∑ j ∈ range (n + 1), q ^ s * (1 / 2 : ℝ) ^ j := by
      apply sum_le_sum_of_injOn (fun i : Fin (n + 1) => i.val - s)
      · intro i hi j hj hij
        apply Fin.ext
        have his := (mem_filter.mp hi).2
        have hjs := (mem_filter.mp hj).2
        change i.val - s = j.val - s at hij
        omega
      · intro _ hj
        obtain ⟨i, _, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)
      · intro i hi
        have his := (mem_filter.mp hi).2
        calc
          q ^ i.val = q ^ s * q ^ (i.val - s) := by rw [← pow_add, Nat.add_sub_of_le his]
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqhalf _) (pow_nonneg hq _)
      · intro j _ _
        positivity
    _ = q ^ s * ∑ j ∈ range (n + 1), (1 / 2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ q ^ s * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (pow_nonneg hq _)
    _ = _ := mul_comm _ _

theorem canonicalDNFTree_switching {n w : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (s : ℕ) :
    (restrictionLaw n p hp hp1.le).probability
      (fun ρ => s ≤ (canonicalDNFTree F ρ).depth) ≤
      2 * (((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ s := by
  let μ := restrictionLaw n p hp hp1.le
  let q := ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))
  let E := fun i : Fin (n + 1) => fun ρ : PartialAssignment n =>
    s ≤ i.val ∧ ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = i.val
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hcover : μ.probability (fun ρ => s ≤ (canonicalDNFTree F ρ).depth) ≤
      μ.probability (fun ρ => ∃ i : Fin (n + 1), E i ρ) := by
    apply μ.probability_mono
    intro ρ hρ
    obtain ⟨bs, hb, hdepth⟩ := canonicalDNFTree_depth_walk F ρ
    let i : Fin (n + 1) := ⟨DNFQueryBlock.length bs, Nat.lt_succ_of_le hb.length_le_dimension⟩
    exact ⟨i, hρ.trans hdepth, bs, hb, rfl⟩
  have heach (i : Fin (n + 1)) : μ.probability (E i) ≤
      if s ≤ i.val then q ^ i.val else 0 := by
    by_cases his : s ≤ i.val
    · rw [ite_eq_left his]
      apply (μ.probability_mono (fun ρ hρ => hρ.2)).trans
      have hb := canonicalWalk_probability F hF p hp hp1 (h := i.val)
      simpa only [q, mul_pow] using hb
    · rw [ite_eq_right his]
      have he : μ.probability (E i) = 0 := by
        unfold FiniteLaw.probability
        calc
          _ = μ.average (fun _ => 0) := by
            apply congrArg μ.average
            funext ρ
            simp [E, his]
          _ = 0 := μ.average_const 0
      exact he.le
  exact hcover.trans ((μ.probability_exists_le E).trans
    ((sum_le_sum (fun i _ => heach i)).trans (finite_geometric_tail n s q hq0 hq)))

theorem dnf_restriction_has_shallow_tree {n w : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (t : ℕ) :
    (restrictionLaw n p hp hp1.le).probability
      (fun ρ => ¬ ∃ T : BooleanDecisionTree n, T.depth ≤ t ∧
        ∀ x, T.eval x = dnfEval F (ρ.apply x)) ≤
      2 * (((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (t + 1) := by
  apply (FiniteLaw.probability_mono _ ?_).trans
    (canonicalDNFTree_switching F hF p hp hp1 hq (t + 1))
  intro ρ hρ
  have hn : ¬ (canonicalDNFTree F ρ).depth ≤ t := by
    intro ht
    exact hρ ⟨canonicalDNFTree F ρ, ht, canonicalDNFTree_eval F ρ⟩
  omega

end TwoPointCorrelations

end OAI
