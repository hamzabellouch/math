import OAI.NumberTheory.CubicMoment.Decomposition.StoppedActualCommon
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorCutoff

namespace OAI

/-! The full small-square-divisor variance model for the literal stopped
coefficient, obtained by restoring its actual common-factor rows. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_full_model_log_saving
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ) (k H q : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*k) →
      ∀ (d : Eisenstein), primary d → Squarefree d → norm d ≤ (Real.log X)^q →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖divisorDispersionVariance d S β u Φ A-
        (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kc,j,hKc,hcommon⟩ := stopped_early_divisor_common_log_saving (ι := ι)
    hpnt hHuxley hξ hξz hκ Φ hΦ hΦ' k
  obtain ⟨Kn,hKn,hcoprime⟩ := stopped_divisor_coprime_model_log_saving (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H
  let G : ℕ := 6*(j+k)+2*(4*(k+2)+k)+4*q+1
  refine ⟨Kc+Kn,G,by positivity,?_⟩
  filter_upwards [hcommon,hcoprime,stopped_logarithmic_divisor_small hκ q,
    eventually_ge_atTop (Real.exp 2)] with X hcommon hcoprime hsmall hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi d hd hds hdlog e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  change ‖divisorDispersionVariance d S β u Φ A-
    (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A‖ ≤ _
  have hL2 : 2 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hX
  have hL1 : 1 ≤ Real.log X := by linarith
  have hpow (n : ℕ) (hn : n ≤ G) : (Real.log X)^n ≤ R/2 := by
    have hh := pow_le_pow_right₀ hL1 hn
    change 2*(Real.log X)^G ≤ R at hR
    linarith
  have hRpos : 0 < R := by
    have hz := hpow 0 (Nat.zero_le G)
    norm_num at hz
    linarith
  have hR2 : 2 < R := by
    have h1 := hpow 1 (by dsimp [G]; omega)
    linarith
  have hdsmall := hsmall b (norm d) hbXlo hdlog
  have hdR : norm d < R :=
    (hdlog.trans (hpow q (by dsimp [G]; omega))).trans_lt (by linarith)
  have hd4 : (norm d)^4 ≤ R := by
    calc
      _ ≤ ((Real.log X)^q)^4 := pow_le_pow_left₀ (norm_nonneg d) hdlog 4
      _ = (Real.log X)^(4*q) := by rw [←pow_mul,Nat.mul_comm]
      _ ≤ R/2 := hpow _ (by dsimp [G]; omega)
      _ ≤ R := by linarith
  have hRc : (Real.log X)^(6*(j+k)) ≤ R :=
    (hpow _ (by dsimp [G]; omega)).trans (by linarith)
  have hRn : 2*(Real.log X)^(2*(4*(k+2)+k)) ≤ R := by
    have hn := hpow (2*(4*(k+2)+k)) (by dsimp [G]; omega)
    linarith
  have hc := hcommon δ b A u hδ hδone hbXlo hbXhi hAlo hAhi W hW e d hd hdsmall
    j₀ k₀ h Z Q early hj hRc hd4
  have hn := hcoprime δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi d hd hds hdsmall e he hNe j₀ k₀ h Z Q early hj hR2 hdR hRn
  calc
    _ = ‖(divisorDispersionVariance d S β u Φ A-divisorCoprimeDispersionGram d S β u Φ A)+
        (divisorCoprimeDispersionGram d S β u Φ A-
          (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hc hn).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
