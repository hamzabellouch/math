import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedLow

namespace OAI

/-! Arbitrary small-power absorption in the polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_low_scale_power {Y R X B δ : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hX : 0 < X) (_hB : 0 ≤ B) (hδ : 0 < δ)
    (hRY : R ≤ Y^B) (hYX : Y^(-B) ≤ X) :
    R^(3*δ)*X^(-δ) ≤ Y^(4*B*δ) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hRpow : R^(3*δ) ≤ Y^(3*B*δ) := by
    apply (Real.rpow_le_rpow hR.le hRY (by positivity)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  have hXpow : X^(-δ) ≤ Y^(B*δ) := by
    apply (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hYp _) hYX (by linarith)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  calc
    _ ≤ Y^(3*B*δ)*Y^(B*δ) := mul_le_mul hRpow hXpow
      (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [←Real.rpow_add hYp]; congr 1; ring

/-- The low-height completed estimate with arbitrary small losses,
for every fixed angular mode and every polynomial scale range. -/
theorem uniform_metaplectic_completed_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {ι : Type*} {W : ι → ℝ → ℂ} (hW : UniformLogWeights W) (ℓ : ℤ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y X : ℝ, 1 ≤ Y → 0 < X → norm r ≤ Y^B → Y^(-B) ≤ X →
        ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖ ≤
          K*Y^ε*Real.sqrt (norm r) := by
  let δ := min (ε/(4*(B+1))) (1/20000)
  have hden : 0 < 4*(B+1) := by positivity
  have hδ : 0 < δ := lt_min (div_pos hε hden) (by norm_num)
  have hδsmall : δ < 1/10000 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : 4*B*δ ≤ ε := by
    have hh := (le_div_iff₀ hden).mp (min_le_left (ε/(4*(B+1))) (1/20000:ℝ))
    change δ*(4*(B+1)) ≤ ε at hh
    nlinarith
  obtain ⟨K,hK,hbound⟩ := uniform_metaplectic_completed_low hV hW ℓ hδ hδ hδsmall
    (hGamma δ hδ hδsmall)
  refine ⟨K,hK,?_⟩
  intro i r hr hsr Y X hY hX hRY hYX
  have hs := metaplectic_low_scale_power hY (norm_pos_of_ne_zero (primary_ne_zero hr)) hX hB hδ hRY hYX
  have he : δ+2*δ = 3*δ := by ring
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
