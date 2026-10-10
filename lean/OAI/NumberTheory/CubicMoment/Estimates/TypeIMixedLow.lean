import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedWeights

namespace OAI

/-! Type I with the precise radial factor in the mixed term of the
corrected square. The squarefree product model, including common zeros,
is preserved on the right. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem typeI_mixed_low_of_published
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖β r‖ ≤ D*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) := by
  let hP := hW.realPower (-1/6)
  obtain ⟨K,hK,hbound⟩ := typeI_low_log_coefficients hV hP.logarithmicWithLength 0 hGamma hB hD k d
  refine ⟨K,hK,?_⟩
  intro w S β X R U hX hBX hR hU hRU hRhi hS hcut hβ
  let v : Eisenstein → γ × {X : ℝ // 1 ≤ X} := fun r => (w r,⟨X,by linarith⟩)
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hb := hbound v S β X R U hX hBX hR hU hRU hRhi hS
    (fun _ _ => rfl) (fun r hr x hx => by
      change ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x = 0
      rw [hcut r hr x hx,mul_zero]) hβ
  have he : (∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)) =
      ((U^(-1/6:ℝ):ℝ):ℂ)*(∑ r ∈ S, β r*
        (metaplecticAngularSmoothSum r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x) U 0-
          angularSmoothModel r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x) U)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [typeIMixedGauss_eq r _ hUp,typeIMixedModel_eq r _ hUp]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hUp _)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hUp.le _)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
