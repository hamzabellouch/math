import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstOrdinaryTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialNoStopNegligible

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => scaleFirstOrdinaryLowTail m ξ (H X) (T X) X)
        =o[atTop] firstMomentScale := by
  let ε := (1/100-ξ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < 1/100 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ := cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO
    m hpnt hMV hC hcap
  obtain ⟨Ct,hs⟩ := scaleFirstOrdinaryStoppedTail_isLittleO m hpnt hMV hC hHuxley
    hξ (by linarith : ξ ≤ 2/5) hρ hρ₂ hε.le hsmall hgap
  refine ⟨Ct+1,?_⟩
  intro H T hT hH hHX
  have hT' : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X := by
    filter_upwards [hT,eventually_ge_atTop (1:ℝ)] with X ht hX
    exact (pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) (Nat.le_succ Ct)).trans ht
  have hsetup : ∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X ht hH hHX hX
    have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
    exact ⟨hH,hHX,(by linarith : Real.log X ≤ 1+Real.log X).trans
      ((le_self_pow₀ hL (Nat.succ_ne_zero Ct)).trans ht)⟩
  let h : ℝ → ℕ := fun _ => 0
  have hsum := ((hn ξ H T h hsetup).add
    (hs H T h (fun _ => true) hT' hH hHX)).add
      (hs H T h (fun _ => false) hT' hH hHX)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [scaleFirstOrdinaryLowTail_two_stage m ξ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X) (h X)).symm

end CubicFirstMoment

end

end OAI
