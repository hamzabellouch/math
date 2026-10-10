import OAI.NumberTheory.CubicMoment.Decomposition.NoStopCentral
import OAI.NumberTheory.CubicMoment.Estimates.LogPowerSaving

namespace OAI

/-! The complete original no-stop branch is negligible. The only logarithmic
loss is the count of its actual short outer norm intervals. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem noStop_central_isLittleO
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (Ct : ℕ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧
      ∀ (i : ℝ → γ) (R : ℝ → Finset Eisenstein) (v : ℝ → Eisenstein → ℂ)
        (ψ : ℝ → ℝ → ℝ) (w Z Y H X₀ : ℝ → ℝ),
        (∀ᶠ X : ℝ in atTop,
          2 ≤ X ∧ 1 ≤ Real.log X ∧ Real.exp hW.radius ≤ X ∧
          1 ≤ Y X ∧ (Real.exp hW.radius*X)^(κ/4)*Z X ≤ Y X ∧
          2*Y X ≤ X^(51/100:ℝ) ∧ 0 < H X ∧
          (∀ r ∈ R X, primary r) ∧ (∀ r ∈ R X, ‖v X r‖ ≤ M) ∧
          (∀ x, 0 ≤ ψ X x ∧ ψ X x ≤ 1)) →
        (fun X => noStopCenteredValue (R X) (v X) (ψ X) (w X) ρ (Z X)
          (Real.exp hW.radius) ℓ (W (i X)) (H X) ((1+Real.log X)^Ct) X (X₀ X))
          =o[atTop] firstMomentScale := by
  obtain ⟨ρ,K,hρ,hρ₂,hK,hbound⟩ := noStop_central_bound hV hW ℓ hGamma hκ hM Ct
  refine ⟨ρ,hρ,hρ₂,?_⟩
  intro i R v ψ w Z Y H X₀ hsetup
  have hb : (fun X => noStopCenteredValue (R X) (v X) (ψ X) (w X) ρ (Z X)
      (Real.exp hW.radius) ℓ (W (i X)) (H X) ((1+Real.log X)^Ct) X (X₀ X))
      =O[atTop] (fun X : ℝ => (1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hsetup,hbound] with X hX hbX
    obtain ⟨hX,hlog,hBX,hY,hdist,hYX,hH,hR,hv,hψ⟩ := hX
    have hXp : 0 < X := by linarith
    have hL : 0 ≤ 1+Real.log X := by linarith
    have hYX' : Y X ≤ X := by
      have hpower : X^(51/100:ℝ) ≤ X := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1:ℝ) ≤ X by linarith) (by norm_num : (51/100:ℝ) ≤ 1)
      linarith
    have hlogs : 1+Real.log (Y X) ≤ 1+Real.log X :=
      by simpa only [add_comm] using add_le_add_left (Real.log_le_log (zero_lt_one.trans_le hY) hYX') 1
    have he := hbX (i X) (R X) (v X) (ψ X) (w X) (Z X) (Y X) (H X) (X₀ X)
      hX hlog hBX hY hdist hYX hH hR hv hψ
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ K*(1+Real.log (Y X))*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := he
      _ ≤ K*(1+Real.log X)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
        gcongr
      _ = K*((1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ)) := by rw [pow_succ]; ring
  exact hb.trans_isLittleO (log_power_powerSaving_isLittleO (Ct+1) (by norm_num))

end CubicFirstMoment

end

end OAI
