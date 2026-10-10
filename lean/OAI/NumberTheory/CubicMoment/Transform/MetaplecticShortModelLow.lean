import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSelectedOuter
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortOuter
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCutoffPowers

namespace OAI

/-! Power-saving forms of the actual short completion error and the
nonzero-angular lattice model, with the source level geometry. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.metaplectic_short_low_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U C : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → 0 ≤ C → C ≤ X →
      R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^(41/50:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_selected_short hV ℓ hGamma
    (by norm_num : 0 < κ) (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨K*D*Real.sqrt 2,by positivity,?_⟩
  intro w S α X R U C hX hR hU hRU hC hCX hscale hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left (by linarith) hR
  have hXsq : X ≤ X^2 := by nlinarith
  have hXX : 2*X ≤ X^2 := by nlinarith [mul_nonneg hXp.le (show 0 ≤ X-2 by linarith)]
  have hNr : 2*R ≤ X^2 := (by linarith : 2*R ≤ 2*X).trans hXX
  have hlow : X^(-(2:ℝ)) ≤ U := by
    exact (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : -(2:ℝ) ≤ 0)).trans
      (by simpa only [Real.rpow_zero] using hU)
  have hb := hbound w S α X (2*R) U C hX1 (by positivity) hC hS (by
    intro r hr
    rw [hY r hr]
    exact ⟨le_rfl,hlow,by simpa only [Real.rpow_two] using hUX.trans hXsq,
      by simpa only [Real.rpow_two] using hCX.trans hXsq,
      by simpa only [Real.rpow_two] using (hS r hr).2.2.trans hNr⟩)
  apply hb.trans
  calc
    _ ≤ K*X^κ*Real.sqrt (2*R)*C^(3/2:ℝ)*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*D)*((X^κ*X^κ)*(R*Real.sqrt (2*R))*C^(3/2:ℝ)) := by ring
    _ = (K*D*Real.sqrt 2)*X^(2*κ)*(R^(3/2:ℝ)*C^(3/2:ℝ)) := by
      rw [short_completion_level_scale hRp,←Real.rpow_add hXp]
      have he : κ+κ = 2*κ := by ring
      rw [he]
      ring
    _ ≤ (K*D*Real.sqrt 2)*X^(2*κ)*X^(159/200:ℝ) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (K*D*Real.sqrt 2)*X^(2*κ+159/200) := by rw [Real.rpow_add hXp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)

theorem LogarithmicWeightFamily.angular_model_low_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := hW.angular_selected_model hℓ
    (by norm_num : 0 < κ) (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/6)
  refine ⟨K*D,mul_nonneg hK hD,?_⟩
  intro w S α X R U hX hR hU hRU hRhi hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hb := hbound w S α X R U hX1 hRp hU hS hY
  have hp := angular_model_level_power hR hU (by simpa only [hRU] using hRhi)
  rw [hRU] at hp
  apply hb.trans
  calc
    _ ≤ K*X^κ*R^(κ-1/6)*U^(1/3:ℝ)*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*D)*(X^κ*X^κ)*(R*(R^(κ-1/6)*U^(1/3:ℝ))) := by ring
    _ = (K*D)*X^(2*κ)*R^κ*(R^(5/6:ℝ)*U^(1/3:ℝ)) := by
      rw [angular_model_outer_power hRp hUp,←Real.rpow_add hXp]
      have he : κ+κ = 2*κ := by ring
      rw [he]
      ring
    _ ≤ (K*D)*X^(2*κ)*X^κ*X^(589/1000:ℝ) := by
      gcongr
    _ = (K*D)*((X^(2*κ)*X^κ)*X^(589/1000:ℝ)) := by ring
    _ = (K*D)*X^(3*κ+589/1000) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (mul_nonneg hK hD)

end CubicFirstMoment

end

end OAI
