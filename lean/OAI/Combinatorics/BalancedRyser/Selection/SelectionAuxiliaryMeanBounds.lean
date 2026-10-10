import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensoredMeans

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem finite_weighted_rescaled_mean {A : Type*} [Fintype A]
    (w Y : A → ℝ) (x a b : ℝ) (hw : ∑ r, w r = 1) (hb : b ≠ 0) :
    (∑ r, w r * (Y r / b - x / a)) =
      ((∑ r, w r * Y r) - (b / a) * x) / b := by
  simp_rw [mul_sub, ← mul_div_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_mul, hw, one_mul]
  field_simp

theorem domain_scale_ratio (p : Parameters) {q t : ℕ}
    (hscale : p.sizeScale q t ≠ 0) :
    p.sizeScale q (t + 1) / p.sizeScale q t = 1 - p.alpha q := by
  unfold Parameters.sizeScale at *
  rw [pow_succ, mul_div_cancel_left₀ _ hscale]

theorem domainTrack_noise_drift_bound {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    |∑ r : Noise I V, noiseWeight p q G S r *
      domainTrackIncrement p q t G i (some S) (some r)| ≤
        (q : ℝ) * domainOverflowMass p q G S i / p.smin := by
  have hsn := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  have hso := (Parameters.source_scale_bounds hp hq hPq hG.1 (by omega : t ≤
    p.lastMainTime q (Fintype.card I))).1
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hn : 0 < p.sizeScale q (t + 1) := hsmin.trans_le hsn
  have ho : 0 < p.sizeScale q t := hsmin.trans_le hso
  have hw := sum_noiseWeight p q G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1)
  have he := censoredDomain_mean_error hG S hpre i hi
  simp only [domainTrackIncrement, hi, ite_true]
  rw [finite_weighted_rescaled_mean _ _ _ _ _ hw hn.ne', domain_scale_ratio p ho.ne',
    abs_div, abs_of_pos hn, abs_of_nonneg he.1]
  exact (div_le_div_of_nonneg_right he.2 hn.le).trans
    (div_le_div_of_nonneg_left (he.1.trans he.2) hsmin hsn)

omit [Fintype V] in

theorem degree_scale_ratio_of_card {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (_hG : Fintype.card I = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hcard : S.remaining.card = Fintype.card I - t) :
    p.degreeScale q (Fintype.card I) (t + 1) / p.degreeScale q (Fintype.card I) t =
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by
  have htn : t < Fintype.card I :=
    (Nat.lt_of_succ_le ht).trans_le (Nat.sub_le _ _)
  have h := SelectionScales.degree_ratio (Parameters.Pstar_pos hp).le
    (show 0 < q by omega) hPq htn
  simpa only [Parameters.degreeScale, Parameters.sizeScale, Parameters.alpha,
    SelectionScales.degree, SelectionScales.domain, hcard, one_div] using h

theorem degreeTrack_noise_drift_bound {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card = Fintype.card I - t) (v : V)
    (hv : v ∈ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      degreeTrackIncrement p q t G v (some S) (some r)) ≤
        p.C * q * degreeCensorMass p q G S v / (p.smin * p.a / 3) := by
  have hsn := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).2.2.1
  have hmin : 0 < p.smin * p.a / 3 := by
    have hs : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    positivity
  have hn : 0 < p.degreeScale q (Fintype.card I) (t + 1) := hmin.trans_le hsn
  have hw := sum_noiseWeight p q G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1)
  have he := censoredDegree_mean_le hG S hpre v
  have hmass : 0 ≤ degreeCensorMass p q G S v := by
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
    · exact le_rfl
  simp only [degreeTrackIncrement, hv, ite_true]
  rw [finite_weighted_rescaled_mean _ _ _ _ _ hw hn.ne',
    degree_scale_ratio_of_card hp hq hPq hG.1 ht S hcard]
  apply (div_le_div_of_nonneg_right (by linarith :
    (∑ r, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) -
      ((1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹)) * degree G S v ≤
        p.C * q * degreeCensorMass p q G S v) hn.le).trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg hp.2.1.le (Nat.cast_nonneg q)) hmass) hmin hsn

end Balanced.Selection.Process

end

end OAI
