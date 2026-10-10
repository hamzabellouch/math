import OAI.NumberTheory.TotientAsymptotic.LocalCandidateAbundance
import OAI.NumberTheory.TotientAsymptotic.CandidateNormalHead
import OAI.NumberTheory.TotientAsymptotic.CollisionLogBudget

namespace OAI

/-! The original head only requires normality at the largest local cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_head_normality_decay {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop,
      C*(1+B x)^5*Real.exp (-(m x:ℝ)^4/6) ≤ rho^(m x) := by
  filter_upwards [ford_band_log_upper,
    m_tendsto.eventually (local_normality_geometric_decay hC (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)≤26)),
    m_tendsto.eventually (eventually_ge_atTop 1),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with x hlog hdec hm hB
  have hl : Real.log (6*B x) ≤ 26*(m x:ℝ) := by
    simpa [fordBandScale] using hlog 0 (by omega)
  have hh := hdec (B x) hB hl 0 (Nat.zero_le _)
  simp only [pow_zero,mul_one] at hh
  have hpow : (1+B x)^5 ≤ (2*B x+2)^6 := by
    apply (pow_le_pow_left₀ (by linarith : (0:ℝ)≤1+B x)
      (by linarith : 1+B x≤2*B x+2) 5).trans
    exact pow_le_pow_right₀ (by linarith : (1:ℝ)≤2*B x+2) (by omega)
  have hm2 : (1:ℝ) ≤ (m x:ℝ)^2 := by
    have hmR : (1:ℝ) ≤ m x := by exact_mod_cast hm
    nlinarith only [hmR]
  have hpos : 0 ≤ C*(2*B x+2)^6*Real.exp (-(m x:ℝ)^4/6) := by positivity
  apply le_trans _ hh
  calc
    _ ≤ C*(2*B x+2)^6*Real.exp (-(m x:ℝ)^4/6) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (Real.exp_pos _).le
    _ ≤ (m x:ℝ)^2*(C*(2*B x+2)^6*Real.exp (-(m x:ℝ)^4/6)) :=
      le_mul_of_one_le_left hpos hm2

/-- Uniform over subsets of the local grid: the head exclusion is negligible
relative to the same prefix volume used by the positive construction. -/
theorem local_non_normal_head_count {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ Q : Finset (Fin (m x-H) → ℕ),
      Q ⊆ gridPrimeTuples (localPrimeGrid x c L (m x-H)) →
      ((nonNormalHeadPairs x (localNormalityScale (m x)) d Q).card:ℝ) ≤
        (x/(d*Real.log x))*rho^(m x)*G x (m x-H) := by
  obtain ⟨C,hC,hcount⟩ := non_normal_head_pair_count
  obtain ⟨D,hD,hmass⟩ := geometric_initial_mass_le_base (half_pos hc)
  intro L
  filter_upwards [hmass,head_limited_prime_coordinates hc] with H hmass hcoord
  filter_upwards [hmass,hcoord,hcount,local_head_normality_decay (mul_pos hC hD),
    capped_prime_tail_denominator hd,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hmass hcoord hcount hdec hdenom hm hB hx1
  intro Q hQ
  let N := m x-H
  have hN : N+H=m x := Nat.sub_add_cancel hm
  have hdata (p) (hp : p ∈ Q) : (∀ i,(p i).Prime) ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) (c/2) ∧
      ∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x :=
    hcoord N hN p (local_grid_tuples_subset (hQ hp))
  have hmass' : (∑ p ∈ Q,reciprocalShiftWeight p) ≤ D*G x N := by
    have hh := hmass N N hN le_rfl Q (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩)
    have he : (Q.image (fun p => primeInitial p N le_rfl))=Q := by
      have hid : (fun p : Fin N → ℕ => primeInitial p N le_rfl)=id := by
        funext p i
        rfl
      rw [hid,Finset.image_id]
    simpa only [he] using hh
  have hprops (p) (hp : p ∈ Q) : (∀ i,(p i).Prime) ∧ StrictAnti p ∧
      Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) :=
    ⟨(hdata p hp).1,prime_coordinates_strictAnti (hdata p hp).1 (hdata p hp).2.1.1.2.1,
      hdenom N (Nat.sub_le _ _) p (hdata p hp).1 (hdata p hp).2.2⟩
  have hh := hcount (localNormalityScale (m x)) (localNormalityScale_gt_two _) d hd N Q hprops
  rw [localNormalityScale_factor] at hh
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hscale : 0 ≤ x/(d*Real.log x) :=
    (div_pos (zero_lt_one.trans hx1) (mul_pos hdR (Real.log_pos hx1))).le
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hfac : 0 ≤ (C*x/(d*Real.log x))*(1+B x)^5*Real.exp (-(m x:ℝ)^4/6) := by
    have hx0 := zero_lt_one.trans hx1
    positivity
  calc
    _ ≤ (C*x/(d*Real.log x))*(1+B x)^5*Real.exp (-(m x:ℝ)^4/6)*
        (D*G x N) := hh.trans (mul_le_mul_of_nonneg_left hmass' hfac)
    _ = (x/(d*Real.log x))*((C*D)*(1+B x)^5*Real.exp (-(m x:ℝ)^4/6))*G x N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hscale) (G_pos hB _).le

end TotientAsymptotic

end

end OAI
