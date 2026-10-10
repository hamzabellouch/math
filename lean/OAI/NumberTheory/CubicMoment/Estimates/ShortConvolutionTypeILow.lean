import OAI.NumberTheory.CubicMoment.Estimates.TypeILogCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.TypeIShortConvolution

namespace OAI

/-! Type I for the actual short Möbius/zeta/log convolution.  The
divisor multiplicity and every logarithmic coefficient factor are proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma short_convolution_divisor_bound (F : ℝ) (S : ι → Finset Eisenstein)
    (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ a ∈ S i, primary a) (hA : ∀ i, ShortArithmeticFactor F (A i))
    (hu : ∀ i, ∀ a ∈ S i, ‖u i a‖ ≤ 1) {b : Eisenstein} (hb : primary b) :
    ‖orderedConvolution S (fun i a =>
      ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a) b‖ ≤
      ((metaplecticPrimaryDivisors b).card:ℝ)^(Fintype.card ι)*
        (1+Real.log (norm b))^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hb0 := primary_ne_zero hb
  have hNb := one_le_norm hb0
  have hL : 0 ≤ 1+Real.log (norm b) := by linarith [Real.log_nonneg hNb]
  have hfdiv (f : ι → Eisenstein) (hf : f ∈ T) (i : ι) : f i ∣ b := by
    rw [←(Finset.mem_filter.mp hf).2]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => metaplecticPrimaryDivisors b) := by
    intro f hf
    apply Fintype.mem_piFinset.mpr
    intro i
    have hfi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨hS i (f i) hfi,norm_le_of_dvd hb0 (hfdiv f hf i)⟩,hfdiv f hf i⟩
  have hc : (T.card:ℝ) ≤ ((metaplecticPrimaryDivisors b).card:ℝ)^(Fintype.card ι) := by
    have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    simpa only [Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Nat.cast_pow] using hh
  change ‖∑ f ∈ T, ∏ i,
    ((MvPowerSeries.coeff (idealExponentOf (f i)) (A i):ℝ):ℂ)*u i (f i)‖ ≤ _
  calc
    _ ≤ ∑ _f ∈ T, (1+Real.log (norm b))^(Fintype.card ι) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      calc
        _ ≤ ∏ _i : ι, (1+Real.log (norm b)) := by
          apply Finset.prod_le_prod₀ (f := fun i => ‖((MvPowerSeries.coeff (idealExponentOf (f i)) (A i):ℝ):ℂ)*u i (f i)‖)
            (g := fun _ => 1+Real.log (norm b)) (fun _ _ => _root_.norm_nonneg _)
          intro i _
          have hfi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i
          exact shortArithmeticFactor_twisted_norm (hA i) hNb
            (mem_primaryElementBall.mpr ⟨hS i (f i) hfi,norm_le_of_dvd hb0 (hfdiv f hf i)⟩)
            _ (hu i (f i) hfi)
        _ = _ := by simp
    _ = (T.card:ℝ)*(1+Real.log (norm b))^(Fintype.card ι) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg hL _)

theorem short_convolution_typeI_low
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ) (S : ι → Finset Eisenstein)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
      (w : Eisenstein → γ) (P : Finset Eisenstein) (X R U : ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, ∀ a ∈ S i, ‖u i a‖ ≤ 1) →
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ P, Y (w r) = X) →
      (∀ r ∈ P, ∀ x : ℝ, B < x → W (w r) x = 0) →
      let α := orderedConvolution S (fun i a =>
        ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a)
      ‖∑ r ∈ P, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  let A₀ : ℝ := (1+Real.log 2)^(Fintype.card ι)
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  obtain ⟨K,hK,hbound⟩ := typeI_low_log_coefficients hV hW ℓ hGamma hB hA₀
    (Fintype.card ι) (Fintype.card ι)
  refine ⟨K,hK,?_⟩
  intro F S A u w P X R U hS hA hu hX hBX hR hU hRU hRhi hP hY hcut
  apply hbound w P _ X R U hX hBX hR hU hRU hRhi hP hY hcut
  intro r hr
  have hXp : 0 < X := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right (by linarith) hU
  have hNr : norm r ≤ 2*X := (hP r hr).2.2.trans (by linarith)
  have hlog : 1+Real.log (norm r) ≤ (1+Real.log 2)*(1+Real.log X) := by
    have hh := Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero (hP r hr).1)) hNr
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXp.ne'] at hh
    have hxlog := Real.log_nonneg (show 1 ≤ X by linarith)
    have h2log := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [mul_nonneg h2log hxlog]
  apply (short_convolution_divisor_bound F S A u hS hA hu (hP r hr).1).trans
  calc
    _ ≤ ((metaplecticPrimaryDivisors r).card:ℝ)^(Fintype.card ι)*
        ((1+Real.log 2)*(1+Real.log X))^(Fintype.card ι) := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (by linarith [Real.log_nonneg (one_le_norm (primary_ne_zero (hP r hr).1))]) hlog _)
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [mul_pow]; dsimp [A₀]; ring

end CubicFirstMoment

end

end OAI
