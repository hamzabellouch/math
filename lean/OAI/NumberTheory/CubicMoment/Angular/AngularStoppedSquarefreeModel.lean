import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCubeMass
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSievedModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSquarefreeModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSievedModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeMass

namespace OAI

/-! The complete positive stopped variance has the true squarefree mass
as its model. Both the divisor sieve and the common-factor terms are actual
finite sums; no variance estimate is assumed. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_squarefree_model_log_saving
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*(k+2*(2*k))) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
      ‖sievedDispersionVariance T S β u Φ A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K,G,hK,hvariance⟩ := angular_stopped_sieved_model_log_saving (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H (2*k)
  obtain ⟨D,hD,hmass⟩ := angular_stopped_cube_mass_log_saving ℓ (ι := ι) hξ hξz hκ Φ hΦ hΦpos hΦ' k
  refine ⟨K+D,G,by positivity,?_⟩
  filter_upwards [hvariance,hmass] with X hvariance hmass
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
  have hv := hvariance δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  have hm := hmass W hW
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early) e b u A hbXlo hbXhi hAlo
  change ‖sievedDispersionVariance T S β u Φ A-
    ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤ _
  calc
    _ ≤ ‖sievedDispersionVariance T S β u Φ A-(finiteSieveDensity T:ℂ)*cubeModelTerm S β u Φ A‖+
        ‖(finiteSieveDensity T:ℂ)*cubeModelTerm S β u Φ A-
          ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := (add_le_add hv hm).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
