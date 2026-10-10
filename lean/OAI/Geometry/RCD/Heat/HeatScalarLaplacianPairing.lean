import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Moving a heat generator onto a scalar Sobolev composition

A bounded gradient suffices for an L² source of the composition. The
original weak Laplacian only needs to lie in L².
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem exists_weakLaplacian_comp_of_bounded_gradient
    (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ u d)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    {Φ φ ψ : ℝ → ℝ} {C D : ℝ≥0} (hΦ : LipschitzWith C Φ) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith D φ) (hφ0 : φ 0=0) (hψ : Continuous ψ)
    (hdΦ : ∀ a, HasDerivAt Φ (φ a) a) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |φ a| ≤ B) (hE : ∀ a, |ψ a| ≤ E) :
    ∃ q : Lp ℝ 2 μ, IsWeakLaplacian μ hQ (SobolevSpace.comp μ hQ hΦ hΦ0 u) q ∧
      q =ᵐ[μ] fun x => φ (SobolevSpace.toLp μ hQ u x)*d x +
        ψ (SobolevSpace.toLp μ hQ u x)*localGamma μ hQ u u x := by
  let U := SobolevSpace.toLp μ hQ u
  have hp : MemLp (fun x => φ (U x)) ∞ μ := memLp_top_of_bound
    (hφ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (U x))
  have hq : MemLp (fun x => ψ (U x)) ∞ μ := memLp_top_of_bound
    (hψ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) E
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (U x))
  have hr : MemLp (fun x => φ (U x)*d x+ψ (U x)*localGamma μ hQ u u x) 2 μ :=
    (hp.mul (Lp.memLp d)).add (hq.mul (localGamma_memLp_of_bounded_gradient μ hQ u u L hL))
  let q := hr.toLp _
  have hrep : q =ᵐ[μ] fun x => φ (U x)*d x+ψ (U x)*localGamma μ hQ u u x := hr.coeFn_toLp
  exact ⟨q,weakLaplacian_comp_C2 μ hQ u d q hd hΦ hΦ0 hφ hφ0 hψ hdΦ hdφ B E hB hE hrep,hrep⟩

variable [μ.Regular]

theorem heat_scalar_inner_laplacian
    (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ u d)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    {Φ φ ψ : ℝ → ℝ} {C D : ℝ≥0} (hΦ : LipschitzWith C Φ) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith D φ) (hφ0 : φ 0=0) (hψ : Continuous ψ)
    (hdΦ : ∀ a, HasDerivAt Φ (φ a) a) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |φ a| ≤ B) (hE : ∀ a, |ψ a| ≤ E)
    (w : Lp ℝ 2 μ) {s : ℝ} (hs : 0 < s) :
    inner ℝ (-heatGeneratorAt μ hQ s w) (hΦ.compLp hΦ0 (SobolevSpace.toLp μ hQ u)) =
      ∫ x, heatAt μ hQ s w x * (φ (SobolevSpace.toLp μ hQ u x)*d x +
        ψ (SobolevSpace.toLp μ hQ u x)*localGamma μ hQ u u x) ∂μ := by
  obtain ⟨q,hq,hrep⟩ := exists_weakLaplacian_comp_of_bounded_gradient μ hQ u d hd L hL
    hΦ hΦ0 hφ hφ0 hψ hdΦ hdφ B E hB hE
  change inner ℝ (-heatGeneratorAt μ hQ s w)
    (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hΦ hΦ0 u)) = _
  rw [heatGeneratorAt_of_pos μ hQ s hs,inner_neg_left,← heatGenerator_form,
    energyForm_comm,hq,neg_neg,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  simp only [Real.inner_apply,hx,heatSobolev_toLp]
  ring

end RegularPointCoordinates

end

end OAI
