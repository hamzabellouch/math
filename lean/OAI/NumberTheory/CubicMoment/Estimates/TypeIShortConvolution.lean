import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionMass

namespace OAI

/-! Type I for the actual short-factor convolution, with its coefficient
mass derived rather than assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma one_add_log_level_le {R U : ℝ} (hR : 1 ≤ R) (hU : 1 ≤ U) (hX : 2 ≤ R*U) :
    1+Real.log R ≤ (1+1/Real.log 2)*Real.log (R*U) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (R*U) := Real.log_le_log (by norm_num) hX
  have hlogR : Real.log R ≤ Real.log (R*U) := Real.log_le_log hRp
    (le_mul_of_one_le_right hRp.le hU)
  have hdiv : 1 ≤ Real.log (R*U)/Real.log 2 := (one_le_div hL).mpr hlog
  calc
    _ ≤ Real.log (R*U)/Real.log 2+Real.log (R*U) := add_le_add hdiv hlogR
    _ = _ := by ring

lemma short_dyadic_mass_for_typeI (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hu : ∀ i, ∀ a ∈ primaryElementBall (2*X i), ‖u i a‖ ≤ 1)
    {R U : ℝ} (hR : 1 ≤ R) (hU : 1 ≤ U) (hRU : 2 ≤ R*U)
    (hprod : (∏ i, X i) ≤ R) (S : Finset Eisenstein)
    (hS : S ⊆ orderedConvolutionSupport (fun i => primaryElementBall (2*X i))) :
    (∑ b ∈ S, ‖orderedConvolution (fun i => primaryElementBall (2*X i))
      (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖) ≤
      ((36*(1+Real.log 2))*(1+1/Real.log 2))^(Fintype.card ι)*R*
        (Real.log (R*U))^(Fintype.card ι) := by
  have hm := short_dyadic_convolution_mass F X A u hA hX hu hR hprod
  have hsub : (∑ b ∈ S, ‖orderedConvolution (fun i => primaryElementBall (2*X i))
      (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖) ≤
      ∑ b ∈ orderedConvolutionSupport (fun i => primaryElementBall (2*X i)),
        ‖orderedConvolution (fun i => primaryElementBall (2*X i))
          (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => _root_.norm_nonneg _)
  apply hsub.trans (hm.trans _)
  have hl := pow_le_pow_left₀ (by linarith [Real.log_nonneg hR])
    (one_add_log_level_le hR hU hRU) (Fintype.card ι)
  calc
    _ ≤ (36*(1+Real.log 2))^(Fintype.card ι)*R*
        (((1+1/Real.log 2)*Real.log (R*U))^(Fintype.card ι)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by simp only [mul_pow]; ring

/-- The zero-angular Type-I height estimate for the literal finite
convolution of short Möbius, zeta and logarithmic factors. -/
theorem short_convolution_typeI_height {W : Eisenstein → ℝ → ℂ}
    (hW : UniformLogWeights W) {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (D : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (F₀ : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
      (R U T : ℝ) (S : Finset Eisenstein),
      (∀ i, ShortArithmeticFactor F₀ (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (2*X i), ‖u i a‖ ≤ 1) →
      1 ≤ R → 1 ≤ U → 1 ≤ T → 2 ≤ R*U → (∏ i, X i) ≤ R →
      S ⊆ orderedConvolutionSupport (fun i => primaryElementBall (2*X i)) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      let a := orderedConvolution (fun i => primaryElementBall (2*X i))
        (fun i b => ((MvPowerSeries.coeff (idealExponentOf b) (A i):ℝ):ℂ)*u i b)
      ((∫ t in T..2*T, ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖)+
       (∫ t in -(2*T)..(-T), ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖))/T ≤
        C*(R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T+
        E*(R*U)^(5/6:ℝ)*(Real.log (R*U))^(Fintype.card ι)/T^D := by
  let K : ℝ := ((36*(1+Real.log 2))*(1+1/Real.log 2))^(Fintype.card ι)
  have hK : 0 ≤ K := by
    have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_height_of_published hW hF hGrowth hHB
    hε D (Fintype.card ι) hK
  refine ⟨C,E,hC,hE,?_⟩
  intro F₀ X A u R U T S hA hX hu hR hU hT hRU hprod hS hlevels
  exact hbound S _ R U T hR hU hT hlevels
    (short_dyadic_mass_for_typeI F₀ X A u hA hX hu hR hU hRU hprod S hS)

end CubicFirstMoment

end

end OAI
