import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBaseScalarValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialLow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMainConstant

namespace OAI

/-! Centering the actual completed transform with its now determined
radial constant, at every fixed angular mode. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaActualCompletedRadialMain_eq {r : Eisenstein} (hr : primary r)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X=metaplecticMain r 0 W X := by
  simpa only [cubicThetaArithmeticBaseScalar_eq_one,star_one,mul_one] using
    cubicThetaActualCompletedRadialMain_mul_base hr W hX

theorem uniform_cubicTheta_centered_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  by_cases hℓ : ℓ=0
  · subst ℓ
    obtain ⟨K,hK,h⟩ := uniform_cubicTheta_radial_remainder_low hW hε hσ
    refine ⟨K,hK,?_⟩
    intro i r hr hs X hX
    simpa only [cubicThetaActualCompletedRadialMain_eq hr (W i) hX] using h i r hr hs X hX
  · obtain ⟨K,hK,h⟩ := uniform_cubicTheta_completed_low hW hℓ hε hσ
    refine ⟨K,hK,?_⟩
    intro i r hr hs X hX
    simpa only [metaplecticMain,ite_eq_right hℓ,sub_zero] using h i r hr hs X hX

theorem uniform_cubicTheta_centered_subpower
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) {ε B : ℝ} (hε : 0<ε) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y X : ℝ, 1≤Y → 0<X → norm r≤Y^B → Y^(-B)≤X →
        ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖≤K*Y^ε*Real.sqrt (norm r) := by
  let δ := ε/(4*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδε : 4*B*δ≤ε := by
    have hh : δ*(4*(B+1))=ε := by dsimp [δ]; field_simp
    nlinarith
  obtain ⟨K,hK,hbound⟩ := uniform_cubicTheta_centered_low hW ℓ hδ hδ
  refine ⟨K,hK,?_⟩
  intro i r hr hsr Y X hY hX hRY hYX
  have hs := metaplectic_low_scale_power hY (norm_pos_of_ne_zero (primary_ne_zero hr)) hX hB hδ hRY hYX
  have he : δ+2*δ=3*δ := by ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hY hδε
  calc
    _ ≤ K*Real.sqrt (norm r)*norm r^(3*δ)*X^(-δ) := by simpa only [he] using hbound i r hr hsr X hX
    _ = (K*Real.sqrt (norm r))*(norm r^(3*δ)*X^(-δ)) := by ring
    _ ≤ (K*Real.sqrt (norm r))*Y^(4*B*δ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (K*Real.sqrt (norm r))*Y^ε := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
