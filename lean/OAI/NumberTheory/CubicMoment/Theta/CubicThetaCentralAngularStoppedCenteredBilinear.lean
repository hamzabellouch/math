import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCenteredBilinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularStoppedCorrectedDispersion

namespace OAI

/-! The actual stopped coefficients satisfy the centered bilinear estimate.
Both energies and the shared-prime correction are derived from their
finite formulas; the early-label roughness condition remains explicit. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_stopped_centered_bilinear_log_saving_actual
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℝ) (hΦnn : ∀ x, 0 ≤ Φ x)
    (hΦ : HasCompactSupport (fun x => (Φ x:ℂ)))
    (hΦpos : tsupport (fun x => (Φ x:ℂ)) ⊆ Set.Ioi 0)
    (hΦ' : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)))
    (hΦone : ∀ x ∈ Set.Icc (1:ℝ) 2, 1 ≤ Φ x)
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0) (k H : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop),
      (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖∑ c ∈ P, ∑ r ∈ S, angularStoppedAlpha ℓ E₀ U ψ w remaining c*β r*
        centeredGauss (c*r)*normTwist u (c*r)‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨Ka,d,hKa,halpha⟩ := stopped_outer_log_energy hpnt
  obtain ⟨Kp,G₀,hKp,hpositive⟩ := angular_stopped_corrected_dispersion_log_saving_actual (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hcut (2*k+d) H
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  let G := max G₀ (d+1+2*k)
  let D := cStar^2*36*18*2*(36*M^2)*Ka/Real.log 2
  refine ⟨d,G,Real.sqrt (Ka*Kp)+Real.sqrt D+1,by positivity,?_⟩
  filter_upwards [hpositive,hcoeff,eventually_ge_atTop (Real.exp 1)]
    with X hpositive hcoeff hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let α := angularStoppedAlpha ℓ E₀ U ψ w remaining
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  have hbp : 0 < b := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hAhi' : A ≤ b^2/(Real.log X)^(3*((2*k+d)+2*(2*(2*k+d)))) := by
    simpa only [show 3*((2*k+d)+2*(2*(2*k+d)))=15*(2*k+d) by omega] using hAhi
  have hAupper : A ≤ b^2 := hAhi.trans
    (div_le_self (sq_nonneg _) (one_le_pow₀ hL1))
  have hR₀ : 2*(Real.log X)^G₀ ≤ R :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (le_max_left _ _)) (by norm_num)).trans hR
  have hR₁ : (Real.log X)^(d+1+2*k) ≤ R := by
    have hh := pow_le_pow_right₀ hL1 (le_max_right G₀ (d+1+2*k))
    change (Real.log X)^(d+1+2*k) ≤ (Real.log X)^G at hh
    change 2*(Real.log X)^G ≤ R at hR
    linarith [pow_nonneg hLp.le G]
  have hRp : 0 < R := (pow_pos hLp _).trans_le hR₁
  have hα : (∑ c ∈ P, ‖α c‖^2) ≤ Ka*A*(Real.log X)^d := by
    change (∑ c ∈ P, ‖angularStoppedAlpha ℓ E₀ U ψ w remaining c‖^2) ≤ _
    rw [angularStoppedAlpha_energy ℓ E₀ U P ψ w remaining (fun c hc => (hP c hc).1)]
    exact halpha E₀ U P ψ w b A X remaining hE₀ hψ hX hb hbXhi hAlo hAupper hP
  have hβ : ∀ r ∈ S, ‖β r‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hS (r : Eisenstein) (hr : r ∈ S) :
      primary r ∧ Squarefree r ∧ b/2 ≤ norm r ∧ norm r ≤ b := by
    have hh := stoppedIntervalSupport_spec X (b/2) b e hr
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hr).2.2.2.1.le,hh.2.2⟩
  have hn (r : Eisenstein) (hr : r ∈ S) (_hz : β r ≠ 0) :
      ((primaryPrimeFactors r).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log (hS r hr).1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log
        (norm_pos_of_ne_zero (primary_ne_zero (hS r hr).1))
        ((hS r hr).2.2.2.trans hbXhi)) (Real.log_pos (by norm_num)).le)
  have hrough (r : Eisenstein) (hr : r ∈ S) (hz : β r ≠ 0)
      (p : Eisenstein) (hp : p ∈ primaryPrimeFactors r) : R ≤ norm p :=
    angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) 0 (1+δ) Z Q W
      (Real.rpow_pos_of_pos hXp _) (Real.rpow_le_rpow_of_exponent_le hX1 hξz)
      (by linarith) (by linarith) j₀ k₀ h early hj hz
      (primaryPrimeFactor_spec (hS r hr).1 hp).1 (primaryPrimeFactor_spec (hS r hr).1 hp).2
  have hp := hpositive δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi' e he hNe j₀ k₀ h Z Q early hj hR₀
  have hcorr := corrected_bilinear_log_saving P S α β u
    (fun c hc => (hP c hc).1) (fun r hr => (hS r hr).1) Φ hΦnn
    hAp hbp hLp hKa.le hKp.le hcut
    (fun c hc => hΦone _ ⟨(le_div_iff₀ hAp).mpr (by simpa using (hP c hc).2.2.1),
      (div_le_iff₀ hAp).mpr (by simpa [mul_comm] using (hP c hc).2.2.2)⟩) k d hα hp
  have hover := bounded_active_model_overlap_log_saving P S α β u hAp hbp hLp hRp hM.le hKa.le
    k d (fun c hc => ⟨(hP c hc).1,(hP c hc).2.2⟩) hS hα hβ hn hrough hR₁
  change ‖∑ c ∈ P, ∑ r ∈ S, α c*β r*centeredGauss (c*r)*normTwist u (c*r)‖ ≤ _
  rw [centered_bilinear_eq_correction_add_overlap P S α β u
    (fun c hc => (hP c hc).1) (fun r hr => ⟨(hS r hr).1,(hS r hr).2.1⟩)]
  apply (norm_add_le _ _).trans ((add_le_add hcorr hover).trans ?_)
  change Real.sqrt (Ka*Kp)*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k+
    Real.sqrt D*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k ≤ _
  calc
    _ = (Real.sqrt (Ka*Kp)+Real.sqrt D)*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith :
          Real.sqrt (Ka*Kp)+Real.sqrt D ≤ Real.sqrt (Ka*Kp)+Real.sqrt D+1)
          (Real.rpow_nonneg hAp.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hLp.le _)

end CubicFirstMoment

end

end OAI
