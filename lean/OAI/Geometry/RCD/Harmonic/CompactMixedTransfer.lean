import OAI.Geometry.RCD.Harmonic.YoungPairingLimit

namespace OAI

/-! # Strong local harmonic recovery transfers a compact-test mixed pairing -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

private theorem gamma_sub_right (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (u w q : SobolevSpace μ hQ) :
    localGamma μ hQ u (w-q)=ᵐ[μ] fun x => localGamma μ hQ u w x-localGamma μ hQ u q x := by
  filter_upwards [localGamma_sub_left μ hQ w q u,localGamma_comm μ hQ u (w-q),
    localGamma_comm μ hQ w u,localGamma_comm μ hQ q u] with x hs hc hw hq
  rw [hc,hs,hw,hq]

theorem compact_mixed_transfer (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω A : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0≤c k)
    (u w q : ℕ → SobolevSpace μ hQ) (F χ : ℕ → X → ℝ)
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hF : ∀ k, AEStronglyMeasurable (F k) (μ.restrict (Ω k)))
    (hχ : ∀ k, AEStronglyMeasurable (χ k) (μ.restrict (Ω k)))
    (hFb : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), |F k x|≤B)
    (hχb : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), |χ k x|≤1)
    (hχone : ∀ k x, x∈A k → χ k x=1)
    (huzero : ∀ k, ∀ᵐ x ∂μ, x∉A k → SobolevSpace.toLp μ hQ (u k) x=0)
    (henergy : ∀ᶠ k in atTop, c k*(∫ x in Ω k, localGamma μ hQ (u k) (u k) x ∂μ)≤C)
    (herror : Tendsto (fun k => c k*∫ x in Ω k, (χ k x)^2*
      localGamma μ hQ (w k-q k) (w k-q k) x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k =>
      c k*(∫ x in Ω k, F k x*localGamma μ hQ (u k) (w k) x ∂μ)-
      c k*(∫ x in Ω k, F k x*localGamma μ hQ (u k) (q k) x ∂μ))
      atTop (𝓝 0) := by
  let φ := fun k x => F k x*χ k x
  have hφb (k : ℕ) : ∀ᵐ x ∂μ.restrict (Ω k), |φ k x|≤B := by
    filter_upwards [hFb k,hχb k] with x hx hy
    change |F k x*χ k x|≤B
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) hB).trans_eq (mul_one B)
  have hdom : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |φ k x|≤B*|χ k x| := by
    apply Eventually.of_forall
    intro k
    filter_upwards [hFb k] with x hx
    change |F k x*χ k x|≤B*|χ k x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have ht := cutoff_mixed_error_tendsto μ hQ Ω c hc (fun k => w k-q k) u φ χ hB hC
    (fun k => (hF k).mul (hχ k)) hχ hφb hχb hdom henergy herror
  have heq (k : ℕ) :
      (∫ x in Ω k, F k x*localGamma μ hQ (u k) (w k) x ∂μ)-
        (∫ x in Ω k, F k x*localGamma μ hQ (u k) (q k) x ∂μ)=
      ∫ x in Ω k, φ k x*localGamma μ hQ (w k-q k) (u k) x ∂μ := by
    have hi (v : SobolevSpace μ hQ) :
        IntegrableOn (fun x => F k x*localGamma μ hQ (u k) v x) (Ω k) μ :=
      (localGamma_memL1 μ hQ (u k) v).restrict.bdd_mul (hF k)
        ((hFb k).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
    rw [← integral_sub (hi (w k)) (hi (q k))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (huzero k),
      ae_restrict_of_ae (gamma_sub_right μ hQ (u k) (w k) (q k)),
      ae_restrict_of_ae (localGamma_comm μ hQ (w k-q k) (u k)),
      ae_restrict_of_ae (localGamma_zero_on_level μ hQ (u k) (w k-q k) 0)]
      with x hz hsub hcomm hzero
    change F k x*localGamma μ hQ (u k) (w k) x-
      F k x*localGamma μ hQ (u k) (q k) x=_
    dsimp only [φ]
    rw [hcomm,hsub]
    by_cases hx : x∈A k
    · rw [hχone k x hx]
      ring
    · have h0 := hzero (hz hx)
      rw [hsub] at h0
      rw [← mul_sub,h0,mul_zero,mul_zero]
  convert ht using 1
  funext k
  rw [← heq k]
  ring

end RegularPointCoordinates

end

end OAI
