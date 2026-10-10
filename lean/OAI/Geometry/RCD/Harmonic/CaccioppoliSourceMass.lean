import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli
import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # Caccioppoli with local value error and absolute source mass -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem caccioppoli_source_mass (u η : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) {v : X → ℝ} {L B A : ℝ≥0}
    (hv : LipschitzWith L v) (hs : HasCompactSupport v)
    (hb : ∀ x, |v x|≤B) (hn : ∀ x, 0≤v x)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ Q η x|≤A)
    {D : ℝ} (_hD : 0≤D)
    (hvalue : ∀ᵐ x ∂μ, v x≠0 → |SobolevSpace.toLp μ Q u x|≤D)
    (hdi : Integrable (fun x => (v x)^2*|d x|) μ) :
    (∫ x, (SobolevSpace.toLp μ Q η x)^2*(SobolevSpace.minimalSlope μ Q u x)^2 ∂μ) ≤
      2*D*(∫ x, (v x)^2*|d x| ∂μ)+
        4*D^2*(∫ x, (SobolevSpace.minimalSlope μ Q η x)^2 ∂μ) := by
  let M := SobolevSpace.cutoffCLM μ Q hv hs hb hn
  let U := SobolevSpace.toLp μ Q u
  have htest : SobolevSpace.toLp μ Q (M (M u)) =ᵐ[μ] fun x => (v x)^2*U x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ Q hv hs hb hn (M u),
      SobolevSpace.cutoffCLM_coe μ Q hv hs hb hn u] with x hx hy
    change SobolevSpace.toLp μ Q (M (M u)) x=v x*SobolevSpace.toLp μ Q (M u) x at hx
    rw [hx,hy]
    ring
  have hsource : Integrable (fun x => d x*((v x)^2*U x)) μ :=
    ((Lp.memLp d).integrable_mul (Lp.memLp (SobolevSpace.toLp μ Q (M (M u))))).congr
      (htest.mono fun x hx => congrArg (fun a => d x*a) hx)
  have hinner : inner ℝ d (SobolevSpace.toLp μ Q (M (M u))) =
      ∫ x, d x*((v x)^2*U x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [htest] with x hx
    simp only [Real.inner_apply,hx]
  have hE : energyForm μ Q u (M (M u))≤D*(∫ x, (v x)^2*|d x| ∂μ) := by
    have he := hd (M (M u))
    rw [hinner] at he
    have hi : (∫ x, -(d x*((v x)^2*U x)) ∂μ)≤
        ∫ x, D*((v x)^2*|d x|) ∂μ := by
      apply integral_mono_ae hsource.neg (hdi.const_mul D)
      filter_upwards [hvalue] with x hx
      change -(d x*((v x)^2*U x))≤D*((v x)^2*|d x|)
      by_cases hz : v x=0
      · simp only [hz,zero_pow (by decide : (2:ℕ)≠0),zero_mul,mul_zero,neg_zero]
        exact le_rfl
      · have hu := hx hz
        calc
          _ ≤ |d x*((v x)^2*U x)| := neg_le_abs _
          _ = ((v x)^2*|d x|)*|U x| := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (v x))]; ring
          _ ≤ ((v x)^2*|d x|)*D := mul_le_mul_of_nonneg_left hu (by positivity)
          _ = _ := by ring
    rw [integral_neg,integral_const_mul] at hi
    linarith only [he,hi]
  have htail : (∫ x, (U x)^2*(SobolevSpace.minimalSlope μ Q η x)^2 ∂μ) ≤
      D^2*(∫ x, (SobolevSpace.minimalSlope μ Q η x)^2 ∂μ) := by
    have hu2 : Integrable (fun x => (U x)^2*(SobolevSpace.minimalSlope μ Q η x)^2) μ :=
      (bounded_square_weight_integrable μ (SobolevSpace.minimalSlope μ Q η) U hgrad).congr
        (Eventually.of_forall fun x => mul_comm _ _)
    have hg2 := (Lp.memLp (SobolevSpace.minimalSlope μ Q η)).integrable_sq
    rw [← integral_const_mul]
    apply integral_mono_ae hu2 (hg2.const_mul (D^2))
    filter_upwards [hvalue,hη,SobolevSpace.minimalSlope_zero_on_level μ Q η 0] with x hx he hz
    by_cases hvx : v x=0
    · rw [hz (he.trans hvx)]
      simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hx hvx) 2) (sq_nonneg _)
  have hc := caccioppoli_cutoffCLM_energy μ Q u η hv hs hb hn hη hgrad
  change _ ≤ 2*energyForm μ Q u (M (M u))+4*(∫ x, (U x)^2*_
    ∂μ) at hc
  nlinarith only [hc,hE,htail]

end RegularPointCoordinates

end

end OAI
