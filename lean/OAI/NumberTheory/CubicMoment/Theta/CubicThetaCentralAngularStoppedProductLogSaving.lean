import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedProductLogSaving
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularStoppedCenteredBilinear

namespace OAI

/-! Full Mellin cancellation for the literal stopped alpha and beta.
The central range uses the proved corrected dispersion; both signed
complements are bounded, so the original smooth product weight remains. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_stopped_product_bilinear_log_saving_actual
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
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0)
    (Ω : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (hΩpos : tsupport Ω ⊆ Set.Ioi 0)
    (hΩsm : ContDiff ℝ ∞ Ω) (k H : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u v A X₀ : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
      0 ≤ v → |u| ≤ (Real.log X)^H → 1+v ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
      2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
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
      ‖centeredProductSmoothed P S (angularStoppedAlpha ℓ E₀ U ψ w remaining) β 0 Ω X₀ u‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  obtain ⟨Kg,Km,dm,Ct,hKg,hKm,htransfer⟩ := angular_stopped_product_transfer ℓ hpnt hMV hC hHuxley
    hM.le Ω hΩ hΩpos hΩsm
  let s := 2*Ct+dm+k+1
  obtain ⟨d,G,Kc,hKc,hpoint⟩ := angular_stopped_centered_bilinear_log_saving_actual (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hΦone hcut k (H+s+2)
  let I := ∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight Ω 1 τ‖
  have hI : 0 ≤ I := integral_nonneg (fun τ => mul_nonneg (abs_nonneg _) (_root_.norm_nonneg _))
  let Km' := Km*M*(4*5^dm)
  have hKm' : 0 ≤ Km' := by dsimp [Km']; positivity
  have hmass : 0 ≤ zeroLineMellinMass Ω := zeroLineMellinMass_nonneg Ω
  have hcs : 0 < cStar := cStar_pos
  let K := zeroLineMellinMass Ω*Kc+Kg+cStar*Km'*I+1
  refine ⟨d,G,K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hcoeff,hpoint,eventually_ge_atTop (Real.exp 2),
    (tendsto_rpow_atTop hκ).eventually_ge_atTop ((65536:ℝ)^2)]
    with X hcoeff hpoint hX hlarge
  intro δ b u v A X₀ hδ hδone hwidth hb hbXlo hbXhi hX₀ hv hu hvF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let L := Real.log X
  let B0 := A^(5/6:ℝ)*b^(5/6:ℝ)
  have hL2 : 2 ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hX
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hbp : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hAl : b^(3/2:ℝ) ≤ A := by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAl
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAl
  have hAupper : A ≤ b^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL1))
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hβ : ∀ r ∈ S, ‖β r‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hS (r : Eisenstein) (hr : r ∈ S) :
      primary r ∧ Squarefree r ∧ b/2 ≤ norm r ∧ norm r ≤ b := by
    have hh := stoppedIntervalSupport_spec X (b/2) b e hr
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hr).2.2.2.1.le,hh.2.2⟩
  have hwindow : (1+Real.log b)^Ct ≤ L^s :=
    stopped_product_window_power hL2 (Real.log_nonneg hb1)
      (Real.log_le_log hbp hbXhi) Ct s (by dsimp [s]; omega)
  have hc : ∀ τ : ℝ, |τ| ≤ (4/3)*L^s →
      ‖centeredProductPolynomial P S (angularStoppedAlpha ℓ E₀ U ψ w remaining) β 0 (u-τ)‖ ≤
        Kc*B0/L^k := by
    intro τ hτ
    have hshift := stopped_product_shift_power hL2 H s hu hτ
    have hh := hpoint δ b (u-τ) v A hδ hδone hwidth hb hbXlo hbXhi hv hshift hvF
      W hW hWi hWd hAl hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
    simpa only [centeredProductPolynomial,theta_zero,mul_one,B0,mul_assoc] using hh
  have ht := htransfer E₀ U P S ψ w remaining β b A X₀ (L^s) u (Kc*B0/L^k)
    (hlarge.trans hbXlo) hAlo hAupper hX₀ hwindow (by positivity) hE₀ hψ hP hS hβ hc
  have hgauss : Kg*B0/L^s ≤ Kg*B0/L^k := by
    simpa only [pow_zero,mul_one] using stopped_product_power_absorb hL1 hB0 hKg.le
      0 k s (by dsimp [s]; omega)
  have hX1 : Real.exp 1 ≤ X := (Real.exp_le_exp.mpr (by norm_num)).trans hX
  have hmodelscale := stopped_product_model_scale hA1 hb1 hX1 hbXhi hAupper dm
  have hmodel : Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm/L^s ≤
      Km'*B0/L^k := by
    apply (div_le_div_of_nonneg_right
      (show Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm ≤
          Km'*B0*L^dm by
        simpa only [Km',B0,L,mul_assoc] using
          mul_le_mul_of_nonneg_left hmodelscale (mul_nonneg hKm.le hM.le))
      (pow_nonneg hLp.le _)).trans
    exact stopped_product_power_absorb hL1 hB0 hKm' dm k s (by dsimp [s]; omega)
  have hgb : Kg*A^(5/6:ℝ)*b^(5/6:ℝ)/L^s = Kg*B0/L^s := by dsimp [B0]; ring
  rw [hgb] at ht
  apply ht.trans
  change zeroLineMellinMass Ω*(Kc*B0/L^k)+Kg*B0/L^s+
    cStar*(Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm/L^s)*I ≤ _
  calc
    _ ≤ zeroLineMellinMass Ω*(Kc*B0/L^k)+Kg*B0/L^k+cStar*(Km'*B0/L^k)*I :=
      add_le_add (add_le_add (le_refl _) hgauss)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmodel cStar_pos.le) hI)
    _ = (zeroLineMellinMass Ω*Kc+Kg+cStar*Km'*I)*B0/L^k := by ring
    _ ≤ K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLp.le _)
      calc
        _ ≤ K*B0 := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hB0
        _ = K*A^(5/6:ℝ)*b^(5/6:ℝ) := by dsimp [B0]; ring

end CubicFirstMoment

end

end OAI
