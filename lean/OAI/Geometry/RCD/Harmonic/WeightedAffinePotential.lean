import OAI.Geometry.RCD.Sobolev.WeightedIntegralPotential

namespace OAI

/-! # Weighted scalar potentials with a nonzero derivative at zero

The weight also belongs to L², so the affine term has a genuine bounded
linear derivative. No constant function is placed in L² on an infinite
measure space.
-/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem weightedIntegralPotential_affine_hasFDerivAt
    (θ : Lp ℝ ∞ μ) (ρ : Lp ℝ 2 μ) (hθ : θ =ᵐ[μ] ρ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, |θ x|≤B)
    {Φ φ : ℝ → ℝ} {C : ℝ≥0} (hd : ∀ a, HasDerivAt Φ (φ a) a)
    (hΦ0 : Φ 0=0) (hφ : LipschitzWith C φ) (f : Lp ℝ 2 μ) :
    let ψ := fun a => φ a-φ 0
    let hψ : LipschitzWith C ψ := by
      simpa only [add_zero] using hφ.sub (LipschitzWith.const (φ 0))
    HasFDerivAt (weightedIntegralPotential μ θ Φ)
      (innerSL ℝ (lpMultiplier μ θ (hψ.compLp (by simp only [ψ,sub_self]) f)+φ 0 • ρ)) f := by
  let c := φ 0
  let ψ := fun a => φ a-c
  let Ψ := fun a => Φ a-c*a
  have hψ : LipschitzWith C ψ := by
    simpa only [add_zero] using hφ.sub (LipschitzWith.const c)
  have hψ0 : ψ 0=0 := sub_self _
  have hΨ0 : Ψ 0=0 := by simp only [Ψ,hΦ0,mul_zero,sub_zero]
  have hD (a : ℝ) : HasDerivAt Ψ (ψ a) a := by
    simpa only [Ψ,ψ,mul_one] using! (hd a).sub ((hasDerivAt_id a).const_mul c)
  have hdiff := weightedIntegralPotential_hasFDerivAt μ θ B hB hD hΨ0 hψ hψ0 f
  have heq (g : Lp ℝ 2 μ) : weightedIntegralPotential μ θ Φ g =
      weightedIntegralPotential μ θ Ψ g+c*inner ℝ ρ g := by
    have hb : ∀ᵐ x ∂μ, ‖θ x‖≤(B:ℝ) := by simpa only [Real.norm_eq_abs] using hB
    have hi := (integralPotential_integrable μ hD hΨ0 hψ hψ0 g).bdd_mul
      (Lp.aestronglyMeasurable θ) hb
    have hj := ((Lp.memLp ρ).integrable_mul (Lp.memLp g)).const_mul c
    unfold weightedIntegralPotential
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    rw [←integral_const_mul]
    have hsum := integral_add hi hj
    simp only [Pi.mul_apply] at hsum
    rw [←hsum]
    apply integral_congr_ae
    filter_upwards [hθ] with x hx
    simp only [hx,Ψ]
    ring
  have hlin : HasFDerivAt (fun g : Lp ℝ 2 μ => c*inner ℝ ρ g)
      (c • innerSL ℝ ρ) f := (innerSL ℝ ρ).hasFDerivAt.const_mul c
  have hder := hdiff.add hlin
  have he : weightedIntegralPotential μ θ Φ = fun g =>
      weightedIntegralPotential μ θ Ψ g+c*inner ℝ ρ g := funext heq
  rw [he]
  simpa only [ψ,c,map_add,map_smul] using! hder

end RegularPointCoordinates

end

end OAI
