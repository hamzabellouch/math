import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryBounds
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessThinning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem finite_censor_mean_error {A : Type*} [Fintype A]
    (w X : A → ℝ) (N : ℝ) (B : A → Prop)
    (hw : ∀ a, 0 ≤ w a) (hX : ∀ a, 0 ≤ X a ∧ X a ≤ N) :
    0 ≤ (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a ∧
      (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a ≤
        N * (∑ a, if B a then w a else 0) := by
  have heq : (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a =
      ∑ a, w a * ((if B a then N else X a) - X a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (hw a)
    split_ifs
    · exact sub_nonneg.mpr (hX a).2
    · exact sub_nonneg.mpr le_rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases h : B a
    · simp only [h, ite_true]
      have hm := mul_le_mul_of_nonneg_left (show N - X a ≤ N by linarith [(hX a).1]) (hw a)
      simpa only [mul_comm N] using hm
    · simp [h]

def domainOverflowMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (i : I) : ℝ :=
  ∑ r : Noise I V, if (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ)
    then noiseWeight p q G S r else 0

def degreeCensorMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (v : V) : ℝ :=
  ∑ r : Noise I V, if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ)
    then noiseWeight p q G S r else 0

theorem censoredDomain_mean_error {p : Parameters} {q t : ℕ}
    {G : Input I V} (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    0 ≤ (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ∧
      (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ≤
          (q : ℝ) * domainOverflowMass p q G S i := by
  have hraw := performed_domain_size p q t G S hpre i hi
  rw [show (fun r : Noise I V =>
      noiseWeight p q G S r * ((domain G S i ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
      (fun r : Noise I V =>
      noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) by
        funext r; rw [Finset.inter_comm]] at hraw
  have herr := finite_censor_mean_error (noiseWeight p q G S)
    (fun r : Noise I V => ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ))
    (domain G S i).card
    (fun r : Noise I V => (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ))
    (noiseWeight_nonnegative_of_precheck p q t G S hpre)
    (fun r => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)⟩)
  change 0 ≤ (∑ r, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
      (∑ r, noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) ∧
    (∑ r, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
      (∑ r, noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) ≤
        (domain G S i).card * domainOverflowMass p q G S i at herr
  rw [hraw] at herr
  refine ⟨herr.1, herr.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (CensoredJumps.domain_card_le_order hG S i)
  apply Finset.sum_nonneg
  intro r _
  split
  · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
  · exact le_rfl

theorem censoredDegree_mean_le {p : Parameters} {q t : ℕ}
    {G : Input I V} (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (v : V) :
    (∑ r : Noise I V, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * degree G S v +
        p.C * q * degreeCensorMass p q G S v := by
  have hraw := performed_degree_le p q t G S hpre hG.2.1 v
  have herr := (finite_censor_mean_error (noiseWeight p q G S)
    (fun r : Noise I V => (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ))
    (degree G S v : ℝ)
    (fun r : Noise I V => r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ))
    (noiseWeight_nonnegative_of_precheck p q t G S hpre)
    (fun r => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (degree_update_le G S r.1 r.2.1 v r.2.2)⟩)).2
  have herr' : (∑ r, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) -
      (∑ r, noiseWeight p q G S r * (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ)) ≤
      (degree G S v : ℝ) * degreeCensorMass p q G S v := by
    convert herr using 1 <;> congr 1
    · apply Finset.sum_congr rfl
      intro r _
      unfold censoredDegreeNumerator
      split_ifs <;> rfl
    · unfold degreeCensorMass
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> rfl
  have hm : (degree G S v : ℝ) * degreeCensorMass p q G S v ≤
      p.C * q * degreeCensorMass p q G S v := by
    apply mul_le_mul_of_nonneg_right (CensoredJumps.current_degree_le_budget hG S v)
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
    · exact le_rfl
  linarith

end Balanced.Selection.Process

end

end OAI
