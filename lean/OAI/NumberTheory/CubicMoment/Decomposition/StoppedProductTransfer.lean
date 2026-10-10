import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductIntegral
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedOuterEnergy

namespace OAI

/-! Full product-weight transfer for the literal stopped outer coefficient.
The beta energy follows from its pointwise bound and primary support;
only the central polynomial estimate is left as a reusable argument. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem stopped_product_transfer (hpnt : PrimaryPrimePNT)
    {C M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ (Kg Km : ℝ) (d Ct : ℕ), 0 < Kg ∧ 0 < Km ∧
      ∀ (E U P B : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop) (β : Eisenstein → ℂ)
        (b A X S u Mc : ℝ),
      (65536:ℝ)^2 ≤ b → 2*b^(3/2:ℝ) ≤ A → A ≤ b^2 → 0 < X →
      (1+Real.log b)^Ct ≤ S → 0 ≤ Mc →
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ n ∈ P, primary n ∧ Squarefree n ∧ A ≤ norm n ∧ norm n ≤ 2*A) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ b/2 ≤ norm n ∧ norm n ≤ b) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∀ τ : ℝ, |τ| ≤ (4/3)*S →
        ‖centeredProductPolynomial P B (stoppedAlpha E U ψ w remaining) β 0 (u-τ)‖ ≤ Mc) →
      ‖centeredProductSmoothed P B (stoppedAlpha E U ψ w remaining) β 0 V X u‖ ≤
        zeroLineMellinMass V*Mc + Kg*A^(5/6:ℝ)*b^(5/6:ℝ)/S +
        cStar*(Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d/S)*
          (∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
  obtain ⟨Ka,da,hKa,halpha⟩ := stopped_outer_log_energy hpnt
  obtain ⟨Kg,Ct,hKg,hgauss⟩ := gauss_mellin_complement_log_saving hpnt hMV hC hHuxley
    hKa.le (show 0 ≤ 18*M^2 by positivity) hM 0 da 0 0 V hV hpos hsm
  obtain ⟨Km,d,hKm,hmodel⟩ := stopped_product_model_norm hpnt
  refine ⟨Kg,Km,d,Ct,hKg,hKm,?_⟩
  intro E U P B ψ w remaining β b A X S u Mc hb hA hAu hX hS hMc hE hψ hP hB hβ hc
  have hbp : 0 < b := by nlinarith
  have hb2 : 2 ≤ b := by nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hAlo : b^(3/2:ℝ) ≤ A := by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hbpow : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hb1
      (by norm_num : (1:ℝ) ≤ 3/2)
  have hbA : b ≤ A := hbpow.trans hAlo
  have hbbig : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
  have hSpos : 0 < S := (pow_pos (by linarith [Real.log_nonneg hb1] : 0 < 1+Real.log b) Ct).trans_le hS
  have hαE : (∑ n ∈ P, ‖stoppedAlpha E U ψ w remaining n‖^2) ≤
      Ka*A*(1+Real.log b)^da := by
    exact (halpha E U P ψ w b A b remaining hE hψ hbbig hb2 le_rfl hAlo hAu hP).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.log_nonneg hb1) (by linarith) da) (by positivity))
  have hβE : (∑ n ∈ B, ‖β n‖^2) ≤ (18*M^2)*b*(1+Real.log b)^0 := by
    have hcard := primary_support_card_le B hbp.le (fun n hn => ⟨(hB n hn).1,(hB n hn).2.2.2⟩)
    calc
      _ ≤ ∑ _n ∈ B, M^2 := Finset.sum_le_sum (fun n hn =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ n hn) 2)
      _ = (B.card:ℝ)*M^2 := by simp
      _ ≤ (18*b)*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
      _ = _ := by ring
  have hg := hgauss P B (stoppedAlpha E U ψ w remaining) β b A X S u hb hA
    (by simpa using hAu) hX hS
    (fun n hn => ⟨(hP n hn).1,
      (le_div_iff₀ hAp).mpr (by simpa using (hP n hn).2.2.1),
      (div_le_iff₀ hAp).mpr (by simpa [mul_comm] using (hP n hn).2.2.2)⟩)
    hB hβ hαE hβE
  simp only [pow_zero,mul_one] at hg
  have hpair (a : Eisenstein) (ha : a ∈ P) (b' : Eisenstein) (hb' : b' ∈ B) :
      A*b/2 ≤ norm (a*b') ∧ norm (a*b') ≤ 2*(A*b) := by
    rw [norm_mul_eq]
    constructor
    · calc
        A*b/2 = A*(b/2) := by ring
        _ ≤ norm a*norm b' := mul_le_mul (hP a ha).2.2.1 (hB b' hb').2.2.1
          (by positivity) (norm_nonneg a)
    · calc
        _ ≤ (2*A)*b := mul_le_mul (hP a ha).2.2.2 (hB b' hb').2.2.2
          (norm_nonneg b') (by positivity)
        _ = _ := by ring
  have hY : Real.exp 1 ≤ 2*(A*b) := by
    have hbprod : b ≤ A*b := le_mul_of_one_le_left hbp.le (by linarith : 1 ≤ A)
    linarith
  have hlogY : 0 ≤ 1+Real.log (2*(A*b)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hY
    rw [Real.log_exp] at hh
    linarith
  have hm := hmodel E U P B ψ w remaining β (A*b/2) (2*(A*b)) M
  exact centered_mellin_integral_bound P B (stoppedAlpha E U ψ w remaining) β
    (fun n hn => (hP n hn).1) (fun n hn => (hB n hn).1) V hV hpos hsm
    hX hSpos hMc
    (show 0 ≤ Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d by positivity) u hc
    (fun t => hm t hE hψ hY (by positivity) hM
      (fun n hn => (hP n hn).1) (fun n hn => (hB n hn).1) hpair hβ) hg

end CubicFirstMoment

end

end OAI
