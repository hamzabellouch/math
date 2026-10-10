import OAI.Geometry.RCD.Coordinates.ShiftedLogarithmJets
import OAI.Geometry.RCD.Sobolev.WeakLaplacianAffineChain
import OAI.Geometry.RCD.Sobolev.BoundedLipschitzMultiplier

namespace OAI

/-! # Sobolev source and Gram data of the actual shifted logarithm

The source is formed from bounded Lipschitz multipliers of the original
Sobolev source and Gram function. It need not be bounded globally.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem shifted_logarithm_regular_data (p : X) (u d G : SobolevSpace μ hQ)
    (hd : IsWeakLaplacian μ hQ u (SobolevSpace.toLp μ hQ d))
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ u u)
    (v : X → ℝ) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hu : SobolevSpace.toLp μ hQ u =ᵐ[μ] v)
    {ε : ℝ} (hε : 0<ε) (A : ℝ≥0) (hval : ∀ x, v x∈Icc 0 (A:ℝ)) :
    ∃ (ℓ S H : SobolevSpace μ hQ) (B C : ℝ≥0),
      IsWeakLaplacian μ hQ ℓ (SobolevSpace.toLp μ hQ S) ∧
      (SobolevSpace.toLp μ hQ H =ᵐ[μ] localGamma μ hQ ℓ ℓ) ∧
      (SobolevSpace.toLp μ hQ ℓ =ᵐ[μ] fun x => Real.log (ε+v x)-Real.log ε) ∧
      LipschitzWith C (fun x => Real.log (ε+v x)-Real.log ε) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ ℓ x|≤B) ∧
      (SobolevSpace.toLp μ hQ S =ᵐ[μ] fun x =>
        SobolevSpace.toLp μ hQ d x/(ε+v x)-localGamma μ hQ u u x/(ε+v x)^2) := by
  obtain ⟨F,F₁,F₂,C,D,J,B,E,hF,hF₁,hF₂,hF0,hdF,hdF₁,hB,hE,he⟩ :=
    shifted_logarithm_jets hε A.coe_nonneg
  let θ := fun x => F₁ (v x)
  let ω := fun x => -F₂ (v x)
  have hθ : LipschitzWith (D*L) θ := hF₁.comp hv
  have hω : LipschitzWith (J*L) ω := (hF₂.comp hv).neg
  have hθb (x : X) : |θ x|≤B := hB _
  have hωb (x : X) : |ω x|≤E := by simpa only [ω,abs_neg] using hE (v x)
  have hθ0 (x : X) : 0≤θ x := by
    rw [show θ x=(ε+v x)⁻¹ from (he _ (hval x)).2.1]
    exact inv_nonneg.mpr (add_nonneg hε.le (hval x).1)
  have hω0 (x : X) : 0≤ω x := by
    rw [show ω x=((ε+v x)^2)⁻¹ by dsimp only [ω]; rw [(he _ (hval x)).2.2,neg_neg]]
    positivity
  let T := d.boundedLipschitzMul μ hQ p hθ hθb hθ0
  let H := G.boundedLipschitzMul μ hQ p hω hωb hω0
  let S := T-H
  let ℓ := SobolevSpace.comp μ hQ hF hF0 u
  have hT := SobolevSpace.boundedLipschitzMul_coe μ hQ d p hθ hθb hθ0
  have hH := SobolevSpace.boundedLipschitzMul_coe μ hQ G p hω hωb hω0
  change SobolevSpace.toLp μ hQ T =ᵐ[μ] fun x => θ x*SobolevSpace.toLp μ hQ d x at hT
  change SobolevSpace.toLp μ hQ H =ᵐ[μ] fun x => ω x*SobolevSpace.toLp μ hQ G x at hH
  have hSr : SobolevSpace.toLp μ hQ S =ᵐ[μ] fun x =>
      F₁ (SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ d x+
        F₂ (SobolevSpace.toLp μ hQ u x)*localGamma μ hQ u u x := by
    filter_upwards [Lp.coeFn_sub (SobolevSpace.toLp μ hQ T) (SobolevSpace.toLp μ hQ H),
      hT,hH,hu,hG] with x hs ht hh hux hg
    change (SobolevSpace.toLp μ hQ T-SobolevSpace.toLp μ hQ H) x = _
    simp only [hs,Pi.sub_apply,ht,hh,hux,hg,θ,ω]
    ring
  have hℓr : SobolevSpace.toLp μ hQ ℓ =ᵐ[μ] fun x => Real.log (ε+v x)-Real.log ε := by
    filter_upwards [SobolevSpace.comp_coe μ hQ hF hF0 u,hu] with x hx hux
    exact hx.trans (by rw [Function.comp_apply,hux]; exact (he _ (hval x)).1)
  have hHr : SobolevSpace.toLp μ hQ H =ᵐ[μ] localGamma μ hQ ℓ ℓ := by
    filter_upwards [hH,hG,hu,localGamma_comp_C1 μ hQ u ℓ hF hF0 hF₁.continuous hdF B hB,
      localGamma_comp_C1_right μ hQ u u hF hF0 hF₁.continuous hdF B hB] with x hh hg hux hleft hright
    change localGamma μ hQ ℓ ℓ x = _ at hleft
    change localGamma μ hQ u ℓ x = _ at hright
    rw [hleft,hright,hux,(he _ (hval x)).2.1]
    rw [hh,hg,show ω x=((ε+v x)^2)⁻¹ by dsimp only [ω]; rw [(he _ (hval x)).2.2,neg_neg]]
    rw [←inv_pow]
    ring
  have hlog : (fun x => Real.log (ε+v x)-Real.log ε) = F ∘ v := by
    funext x
    exact (he _ (hval x)).1.symm
  refine ⟨ℓ,S,H,C*A,C*L,
    weakLaplacian_comp_C2_affine μ hQ u (SobolevSpace.toLp μ hQ d)
      (SobolevSpace.toLp μ hQ S) hd hF hF0 hF₁ hF₂.continuous hdF hdF₁ B E hB hE hSr,
    hHr,hℓr,?_,?_,?_⟩
  · rw [hlog]
    exact hF.comp hv
  · filter_upwards [hℓr] with x hx
    rw [hx,←(he _ (hval x)).1]
    have hb := hF.dist_le_mul (v x) 0
    simp only [hF0,Real.dist_eq,sub_zero,abs_of_nonneg (hval x).1] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hval x).2 C.coe_nonneg)
  · filter_upwards [hSr,hu] with x hx hux
    rw [hx,hux,(he _ (hval x)).2.1,(he _ (hval x)).2.2]
    simp only [div_eq_mul_inv]
    ring

end RegularPointCoordinates

end

end OAI
