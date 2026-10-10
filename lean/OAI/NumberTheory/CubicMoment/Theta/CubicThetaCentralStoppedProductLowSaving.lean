import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductLowSaving
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralStoppedProductLogSaving

namespace OAI

/-! The full stopped product estimate integrated against the actual
low-height multiplier. A finite logarithmic loss is paid explicitly. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem stopped_product_low_log_saving_actual
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
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
    (hΩsm : ContDiff ℝ ∞ Ω) (k Ct : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b v A X₀ H : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
      0 ≤ v → 1+v ≤ (Real.log X)^F → 0 < H →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
      2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*(k+Ct)+d)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop),
      (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U ψ w remaining a*β b*
        centeredHeightKernel 0 Ω H ((1+Real.log X)^Ct) X₀ X₀ (a*b)‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨d,G,K,hK,hbound⟩ := stopped_product_bilinear_log_saving_actual (ι := ι)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hΦone hcut Ω hΩ hΩpos hΩsm (k+Ct) (Ct+2)
  let K' := (8/3)*Real.log 2*(2:ℝ)^Ct*K
  refine ⟨d,G,K',by dsimp [K']; positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (Real.exp ((2:ℝ)^(Ct+2)))] with X hb hX
  intro δ b v A X₀ H hδ hδ1 hwidth hb2 hbκ hbX hX₀ hv hvF hH
    W hW hWs hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hrough E₀ U P ψ w
    remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let α := stoppedAlpha E₀ U ψ w remaining
  let L := Real.log X
  let T := (1+L)^Ct
  have hlog : (2:ℝ)^(Ct+2) ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hL1 : 1 ≤ L := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hlog
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hT : 0 < T := by dsimp [T]; positivity
  have hTc : T ≤ (2:ℝ)^Ct*L^Ct := by
    dsimp [T]
    rw [←mul_pow]
    gcongr
    linarith
  have hphase (t : ℝ) (ht : t ∈ Set.Icc (-(4/3)*T) ((4/3)*T)) :
      |t| ≤ L^(Ct+2) := by
    have ha : |t| ≤ (4/3)*T := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hc : (4/3)*(2:ℝ)^Ct ≤ L^2 := by
      have hpow : (2:ℝ)^(Ct+2) = (2:ℝ)^Ct*4 := by rw [pow_add]; norm_num
      have hbig : (4/3)*(2:ℝ)^Ct ≤ L := by nlinarith [hlog,hpow,pow_nonneg (by norm_num : (0:ℝ) ≤ 2) Ct]
      exact hbig.trans (by nlinarith)
    calc
      _ ≤ (4/3)*((2:ℝ)^Ct*L^Ct) := ha.trans (mul_le_mul_of_nonneg_left hTc (by norm_num))
      _ ≤ L^2*L^Ct := by nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg hLp.le Ct)]
      _ = _ := by rw [pow_add]; ring
  have hsize : 0 ≤ K*A^(5/6:ℝ)*b^(5/6:ℝ)/L^(k+Ct) := by
    have hbp : 0 < b := by linarith
    have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le (by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)] : b^(3/2:ℝ) ≤ A)
    positivity
  rw [centered_product_low_integral P S α β 0 Ω X₀ X₀ T hH]
  have hi := lowHeightWeight_integral_bound H hT hsize
    (fun t => Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
      centeredProductSmoothed P S α β 0 Ω X₀ t) (by
        intro t ht
        rw [norm_mul]
        have hephase : ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)‖ = 1 := by
          simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
            Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,Real.exp_zero]
        rw [hephase,one_mul]
        exact hb δ b t v A X₀ hδ hδ1 hwidth hb2 hbκ hbX hX₀ hv (hphase t ht) hvF
          W hW hWs hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hrough E₀ U P ψ w
          remaining hE₀ hψ hP)
  have heint : (fun t => (lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      centeredProductSmoothed P S α β 0 Ω X₀ t) =
      (fun t => lowHeightWeight H T t*(Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        centeredProductSmoothed P S α β 0 Ω X₀ t)) := by funext t; ring
  rw [heint]
  apply hi.trans
  calc
    _ ≤ (8/3)*Real.log 2*((2:ℝ)^Ct*L^Ct)*
        (K*A^(5/6:ℝ)*b^(5/6:ℝ)/L^(k+Ct)) := by gcongr
    _ = K'*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
      dsimp [K',L]
      rw [pow_add]
      field_simp [show Real.log X ≠ 0 from hLp.ne']

end CubicFirstMoment

end

end OAI
