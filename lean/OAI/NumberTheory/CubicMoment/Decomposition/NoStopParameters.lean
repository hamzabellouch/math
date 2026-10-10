import OAI.NumberTheory.CubicMoment.Decomposition.NoStopNegligible
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The manuscript's actual no-stop threshold is short enough for Type I.
All scale conditions are derived from their strict numerical exponent gaps. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_noStop_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    ∀ᶠ X : ℝ in atTop,
      2 ≤ X ∧ 1 ≤ Real.log X ∧ Real.exp hW.radius ≤ X ∧
      1 ≤ X^(2/5:ℝ) ∧
      (Real.exp hW.radius*X)^((1/100:ℝ)/4)*X^(38/100:ℝ) ≤ X^(2/5:ℝ) ∧
      2*X^(2/5:ℝ) ≤ X^(51/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp hW.radius),
    eventually_const_mul_rpow_le (by norm_num : (1/400:ℝ)+38/100 < 2/5)
      ((Real.exp hW.radius)^(1/400:ℝ)),
    eventually_const_mul_rpow_le (by norm_num : (2/5:ℝ) < 51/100) 2]
    with X hX hlog hBX hdist hshort
  refine ⟨hX,hlog,hBX,Real.one_le_rpow (by linarith) (by norm_num),?_,hshort⟩
  have hXp : 0 < X := by linarith
  have he : (1/100:ℝ)/4 = 1/400 := by norm_num
  rw [he,Real.mul_rpow (Real.exp_pos _).le hXp.le,mul_assoc,←Real.rpow_add hXp]
  exact hdist

theorem noStop_patterson_isLittleO
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {M : ℝ} (hM : 0 ≤ M) (Ct : ℕ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧
      ∀ (i : ℝ → γ) (R : ℝ → Finset Eisenstein) (v : ℝ → Eisenstein → ℂ)
        (ψ : ℝ → ℝ → ℝ) (w H X₀ : ℝ → ℝ),
        (∀ᶠ X : ℝ in atTop,
          0 < H X ∧ (∀ r ∈ R X, primary r) ∧ (∀ r ∈ R X, ‖v X r‖ ≤ M) ∧
          (∀ x, 0 ≤ ψ X x ∧ ψ X x ≤ 1)) →
        (fun X => noStopCenteredValue (R X) (v X) (ψ X) (w X) ρ (X^(38/100:ℝ))
          (Real.exp hW.radius) ℓ (W (i X)) (H X) ((1+Real.log X)^Ct) X (X₀ X))
          =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hbound⟩ := noStop_central_isLittleO hV hW ℓ hGamma
    (by norm_num : (0:ℝ) < 1/100) hM Ct
  refine ⟨ρ,hρ,hρ₂,?_⟩
  intro i R v ψ w H X₀ hsetup
  apply hbound i R v ψ w (fun X => X^(38/100:ℝ)) (fun X => X^(2/5:ℝ)) H X₀
  filter_upwards [hsetup,eventually_noStop_scales hW] with X hs hx
  exact ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2,
    hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

end CubicFirstMoment

end

end OAI
