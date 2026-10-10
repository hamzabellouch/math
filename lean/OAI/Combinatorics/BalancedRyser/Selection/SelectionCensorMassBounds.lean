import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensorProbability
import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensoredMeans
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPostcheckTail
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessScales

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem noise_domain_overflow_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    (∑ r : Noise I V,
      if (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)
      then noiseWeight p q G S r else 0) ≤ postcheckTail p q := by
  exact noise_thinned_tail_le p q t G S hpre (domain G S i) (postcheckMean p)
    (domain_flag_mean_le p q t hq G hG S hpre i)

theorem noise_degree_censor_mass_le (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 0 < q) (G : Input I V)
    (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (v : V)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hremaining : p.a * (q : ℝ) ≤ (S.remaining.card : ℝ)) :
    (∑ r : Noise I V,
      if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q := by
  calc
    _ ≤ (∑ r : Noise I V,
          if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) +
        (∑ r : Noise I V,
          if (q : ℝ) ^ (1 / 8 : ℝ) <
              ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
          then noiseWeight p q G S r else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hn := noiseWeight_nonnegative_of_precheck p q t G S hpre r
      by_cases he : r.2.1 ∈ G.exceptional v <;>
        by_cases ht : (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ) <;>
        simp only [he, ht, true_or, false_or, ite_true, ite_false] <;> linarith
    _ ≤ _ := add_le_add
      (exceptional_noise_mass_le_source_bound p hp hq hG S v hpre hscale hremaining)
      (noise_thinned_tail_le p q t G S hpre (neighbors G v) (postcheckMean p)
        (neighbor_flag_mean_le p q t hq G hG S hpre v))

theorem noise_degree_censor_mass_le_source (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card + t = Fintype.card I) (v : V) :
    (∑ r : Noise I V,
      if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q := by
  apply noise_degree_censor_mass_le p hp q t (by omega) G hG S hpre v
  · exact (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  · have hrem := Parameters.remaining_ge hp (show q ≤ Fintype.card I by
      have hn := hG.1
      omega) ht
    have heq : S.remaining.card = Fintype.card I - t := by omega
    simpa only [heq] using hrem

theorem domainOverflowMass_le_postcheckTail (p : Parameters) (q t : ℕ)
    (hq : 0 < q) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    domainOverflowMass p q G S i ≤ postcheckTail p q :=
  noise_domain_overflow_mass_le p q t hq G hG S hpre i

theorem degreeCensorMass_le_source (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card + t = Fintype.card I) (v : V) :
    degreeCensorMass p q G S v ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q :=
  noise_degree_censor_mass_le_source p hp q t hq hPq G hG ht S hpre hcard v

theorem censoredDomain_mean_error_le_source {p : Parameters} {q t : ℕ}
    (hq : 0 < q) {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I)
    (hi : i ∈ S.remaining) :
    0 ≤ (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ∧
      (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ≤ (q : ℝ) * postcheckTail p q := by
  obtain ⟨hl, hu⟩ := censoredDomain_mean_error hG S hpre i hi
  exact ⟨hl, hu.trans (mul_le_mul_of_nonneg_left
    (domainOverflowMass_le_postcheckTail p q t hq G hG S hpre i) (Nat.cast_nonneg q))⟩

theorem censoredDegree_mean_le_source (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card + t = Fintype.card I) (v : V) :
    (∑ r : Noise I V, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * degree G S v +
        p.C * q * (2 * (q : ℝ) ^ (1 / 8 : ℝ) /
          (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q) := by
  apply (censoredDegree_mean_le hG S hpre v).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (degreeCensorMass_le_source p hp q t hq hPq G hG ht S hpre hcard v)
    (mul_nonneg hp.2.1.le (Nat.cast_nonneg q))

theorem tendsto_polynomial_mul_postcheckTail (p : Parameters) (hp : p.Admissible)
    (r : ℕ) :
    Filter.Tendsto (fun q : ℕ => (q : ℝ) ^ r * postcheckTail p q)
      Filter.atTop (nhds 0) := by
  have hm : 0 ≤ postcheckMean p :=
    mul_nonneg (Parameters.Pstar_pos hp).le
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 p.C))
  exact BernoulliTail.tendsto_polynomial_mul_thinning_tail
    (by norm_num : (0 : ℝ) < 1 / 8) r (Real.exp 1 * postcheckMean p)
    (mul_nonneg (Real.exp_pos 1).le hm)

end Balanced.Selection.Process

end

end OAI
