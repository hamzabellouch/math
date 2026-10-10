import OAI.NumberTheory.TotientAsymptotic.LocalValueNormality
import OAI.NumberTheory.TotientAsymptotic.LocalSquareDecay
import OAI.NumberTheory.TotientAsymptotic.LocalSquareNormality
import OAI.NumberTheory.TotientAsymptotic.CollisionLogBudget

namespace OAI

/-! The original-head exceptions are counted at the ambient endpoint. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma ambient_local_log_bound : ∀ᶠ x : ℝ in atTop,
    Real.log (B x+4) ≤ 26*(m x:ℝ) := by
  filter_upwards [ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop 1),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with x hlog hm hB
  have hh : Real.log (6*B x) ≤ 26*(m x:ℝ) := by
    simpa [fordBandScale] using hlog 0 (by omega)
  exact (Real.log_le_log (by linarith only [hB]) (by linarith only [hB])).trans hh

theorem ambient_nonnormal_witness_count (d q : ℕ) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient ∧ ((d*r.totient:ℕ):ℝ)≤x) →
      (Q.card:ℝ) ≤ x/Real.log x*rho^(m x) := by
  filter_upwards [ambient_local_log_bound,
    m_tendsto.eventually (local_nonnormal_witness_count_rate (A:=26) (by norm_num) 1),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),eventually_ge_atTop (256:ℝ)]
    with x hlog hcount hB hx
  intro R Q F hQR hR hq hbranch hbad hF
  simpa only [one_mul] using hcount x d q hx hB hlog hd R Q F hQR hR hq hbranch hbad hF

theorem ambient_square_witness_count :
    ∀ᶠ x : ℝ in atTop,∀ (Q : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (Q : Set ℕ) →
      (∀ r ∈ Q,0<F r ∧ ((F r).totient:ℝ)≤x) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ localNormalityScale (m x)<p ∧
        (p^2 ∣ F r ∨ p^2 ∣ (F r).totient)) →
      (Q.card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  filter_upwards [ambient_local_log_bound,
    m_tendsto.eventually (local_square_cutoff_le_normality (A:=26) (by norm_num)),
    local_square_witness_power_saving (4:ℝ),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hlog hcut hcount hB hx
  intro Q F hinj hF hbad
  apply hcount Q F hinj hF
  intro r hr
  obtain ⟨p,hp,hlarge,hsq⟩ := hbad r hr
  refine ⟨p,hp,?_,hsq⟩
  exact_mod_cast (hcut x hx hB hlog).trans_lt hlarge

end TotientAsymptotic

end

end OAI
