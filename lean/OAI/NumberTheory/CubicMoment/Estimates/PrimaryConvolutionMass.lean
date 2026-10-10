import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments
import OAI.NumberTheory.CubicMoment.Estimates.TypeIFinal

namespace OAI

/-! Sharp L1 mass of the actual finite primary convolutions. Collection
by product costs no multiplicity loss in L1. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mass_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) :
    (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b‖) ≤
      ∏ i, ∑ a ∈ S i, ‖w i a‖ := by
  calc
    _ ≤ ∑ b ∈ orderedConvolutionSupport S,
        ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b, ‖∏ i, w i (f i)‖ :=
      Finset.sum_le_sum (fun b _ => norm_sum_le _ _)
    _ = ∑ f ∈ Fintype.piFinset S, ‖∏ i, w i (f i)‖ :=
      Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _
    _ = _ := by
      simp only [norm_prod]
      exact (Finset.prod_univ_sum S (fun i a => ‖w i a‖)).symm

lemma primaryConvolution_mass_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (X M : ι → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hM : ∀ i, 0 ≤ M i) (hS : ∀ i, S i ⊆ primaryElementBall (X i))
    (hw : ∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) :
    (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b‖) ≤
      18^(Fintype.card ι)*(∏ i, X i)*(∏ i, M i) := by
  apply (orderedConvolution_mass_le S w).trans
  calc
    _ ≤ ∏ i, (18*X i*M i) := by
      apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
      intro i hi
      calc
        _ ≤ ∑ _a ∈ S i, M i := Finset.sum_le_sum (fun a ha => hw i a ha)
        _ = ((S i).card:ℝ)*M i := by simp
        _ ≤ (18*X i)*M i := mul_le_mul_of_nonneg_right
          ((Nat.cast_le.mpr (Finset.card_le_card (hS i))).trans (primaryElementBall_card_le (hX i)))
          (hM i)
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

lemma short_convolution_mass (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hu : ∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) :
    (∑ b ∈ orderedConvolutionSupport (fun i => primaryElementBall (X i)),
      ‖orderedConvolution (fun i => primaryElementBall (X i))
        (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖) ≤
      18^(Fintype.card ι)*(∏ i, X i)*(∏ i, (1+Real.log (X i))) := by
  exact primaryConvolution_mass_le _ _ X (fun i => 1+Real.log (X i))
    (fun i => zero_le_one.trans (hX i)) (fun i => by linarith [Real.log_nonneg (hX i)])
    (fun _ => Finset.Subset.refl _) (fun i a ha =>
      shortArithmeticFactor_twisted_norm (hA i) (hX i) ha _ (hu i a ha))

private lemma factor_le_total_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  have hr : 1 ≤ ∏ j ∈ Finset.univ.erase i, X j :=
    Finset.one_le_prod₀ (fun j _ => hX j)
  calc
    X i ≤ (∏ j ∈ Finset.univ.erase i, X j)*X i :=
      le_mul_of_one_le_left (zero_le_one.trans (hX i)) hr
    _ = _ := Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- Actual short Möbius/zeta/log coefficients on fixed dyads have only
linear length mass and a fixed logarithmic power. -/
theorem short_convolution_mass_log (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hu : ∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1)
    {R : ℝ} (hR : 1 ≤ R) (hprod : (∏ i, X i) ≤ R) :
    (∑ b ∈ orderedConvolutionSupport (fun i => primaryElementBall (X i)),
      ‖orderedConvolution (fun i => primaryElementBall (X i))
        (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖) ≤
      18^(Fintype.card ι)*R*(1+Real.log R)^(Fintype.card ι) := by
  apply (short_convolution_mass F X A u hA hX hu).trans
  have hlogs : (∏ i, (1+Real.log (X i))) ≤ (1+Real.log R)^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, (1+Real.log R) := Finset.prod_le_prod₀
        (fun i _ => by linarith [Real.log_nonneg (hX i)])
        (fun i _ => add_le_add le_rfl (Real.log_le_log
          (zero_lt_one.trans_le (hX i)) ((factor_le_total_product X hX i).trans hprod)))
      _ = _ := by simp
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hprod (by positivity)) hlogs
    (Finset.prod_nonneg (fun i _ => by linarith [Real.log_nonneg (hX i)]))
    (by positivity)

/-- The usual dyadic supports `[X_i,2 X_i]`, with the lower cutoff
allowed inside the bounded twist, give the precise coefficient mass
needed for the Type-I level dyad. -/
theorem short_dyadic_convolution_mass (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hu : ∀ i, ∀ a ∈ primaryElementBall (2*X i), ‖u i a‖ ≤ 1)
    {R : ℝ} (hR : 1 ≤ R) (hprod : (∏ i, X i) ≤ R) :
    (∑ b ∈ orderedConvolutionSupport (fun i => primaryElementBall (2*X i)),
      ‖orderedConvolution (fun i => primaryElementBall (2*X i))
        (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖) ≤
      (36*(1+Real.log 2))^(Fintype.card ι)*R*(1+Real.log R)^(Fintype.card ι) := by
  have hX₂ (i : ι) : 1 ≤ 2*X i := by linarith [hX i]
  apply (short_convolution_mass F (fun i => 2*X i) A u hA hX₂ hu).trans
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog (i : ι) : 1+Real.log (2*X i) ≤ (1+Real.log 2)*(1+Real.log R) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (zero_lt_one.trans_le (hX i)).ne']
    have hx := Real.log_le_log (zero_lt_one.trans_le (hX i))
      ((factor_le_total_product X hX i).trans hprod)
    nlinarith [mul_nonneg hlog2 hlogR]
  have hlogs : (∏ i, (1+Real.log (2*X i))) ≤
      ((1+Real.log 2)*(1+Real.log R))^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, ((1+Real.log 2)*(1+Real.log R)) :=
        Finset.prod_le_prod₀ (fun i _ => by linarith [Real.log_nonneg (hX₂ i)])
          (fun i _ => hlog i)
      _ = _ := by simp
  have hprod₂ : (∏ i, 2*X i) ≤ 2^(Fintype.card ι)*R := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  calc
    _ ≤ 18^(Fintype.card ι)*(2^(Fintype.card ι)*R)*
        (((1+Real.log 2)*(1+Real.log R))^(Fintype.card ι)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod₂ (by positivity)) hlogs
        (Finset.prod_nonneg (fun i _ => by linarith [Real.log_nonneg (hX₂ i)]))
        (by positivity)
    _ = _ := by rw [show (36:ℝ) = 18*2 by norm_num]; simp only [mul_pow]; ring

end CubicFirstMoment

end

end OAI
