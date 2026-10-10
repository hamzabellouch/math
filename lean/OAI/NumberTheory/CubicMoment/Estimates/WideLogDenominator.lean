import OAI.NumberTheory.CubicMoment.Estimates.UniformLogDenominator
import OAI.NumberTheory.CubicMoment.Estimates.NormalizedCoordinateMoments

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

def wideLogWeightParameters (c : ℝ) : Set (ℝ × ℝ) := Icc c 2 ×ˢ Icc 0 1

lemma wideLogWeightParameters_compact (c : ℝ) : IsCompact (wideLogWeightParameters c) :=
  isCompact_Icc.prod isCompact_Icc

 def uniformWideLogDenominatorWeights {γ : Type*} {c : ℝ} (hc : 0 < c)
    {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) :
    UniformLogWeights (fun z : γ × wideLogWeightParameters c => logDenominatorWeight c (W z.1) z.2) := by
  let F : (ℝ × ℝ) → ℝ → ℂ :=
    fun p x => (smoothReciprocal c (p.1+p.2*smoothLog x):ℂ)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    have hD : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
        z.1.1+z.1.2*smoothLog z.2) := by
      have hL := smoothLog_smooth.comp
        (contDiff_snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => z.2))
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp ((smoothReciprocal_smooth hc).comp hD)
  exact hW.compactMultiplier (wideLogWeightParameters c) (wideLogWeightParameters_compact c) F hF

 def uniformCoordinateWideLogDenominatorWeights {γ ι : Type*} [Fintype ι]
    {c : ℝ} (hc : 0 < c) {W : γ → ι → ℝ → ℂ}
    (hW : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) :
    UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι =>
      logDenominatorWeight c (W z.1.1 z.2) (z.1.2 z.2)) := by
  exact (uniformWideLogDenominatorWeights hc hW).reindex
    (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => ((z.1.1,z.2),z.1.2 z.2))

lemma wideLogWeightParameters_mem {c Y X : ℝ} (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y)
    (hlo : Y^c ≤ X) (hhi : X ≤ Y^2) :
    (Real.log X/Real.log Y,1/Real.log Y) ∈ wideLogWeightParameters c := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  refine ⟨⟨?_,?_⟩,⟨by positivity,?_⟩⟩
  · apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    nlinarith
  · apply (div_le_iff₀ hlogY).mpr
    have h := Real.log_le_log hX hhi
    rw [Real.log_pow] at h
    norm_num at h ⊢
    linarith
  · exact (one_div_le_one_div_of_le (by norm_num) hY).trans_eq (by norm_num)

lemma logDenominatorWeight_scale_lower {c Y X x : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hx : 1 ≤ x)
    (w : ℝ → ℂ) :
    logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) x =
      (Real.log Y:ℂ)*w x/(Real.log (X*x):ℂ) := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  have hp : c ≤ Real.log X/Real.log Y := by
    apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    linarith
  have hx0 : 0 < x := by linarith
  rw [logDenominatorWeight_eq hc w hp (by positivity) hx,Real.log_mul hX.ne' hx0.ne']
  push_cast
  have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogY.ne'
  field_simp

lemma normalizedVonMangoldt_weight_lower {c Y X : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X)
    (w : ℝ → ℂ) (hw : ∀ x, x < 1 → w x = 0) (a : Eisenstein) :
    (normalizedVonMangoldt a:ℂ)*w (norm a/X) =
      (1/(Real.log Y:ℂ))*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) (norm a/X) := by
  by_cases hx : 1 ≤ norm a/X
  · have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
    rw [logDenominatorWeight_scale_lower hc hY0 hY hlo hx]
    have he : X*(norm a/X) = norm a := by field_simp
    rw [he]
    unfold normalizedVonMangoldt
    push_cast
    have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    field_simp
  · have hz := hw _ (lt_of_not_ge hx)
    simp only [hz,mul_zero,logDenominatorWeight]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryNormalizedVonMangoldtTuple_eq_lower {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryNormalizedVonMangoldtTuple primaryCoordinateWeightedTuple primaryTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight_lower hc hY0 hY (hXlo _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

lemma normalizedCoordinate_norm_le_lower {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    ‖primaryNormalizedVonMangoldtTuple a b q η t W X V Y‖ ≤
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryNormalizedVonMangoldtTuple_eq_lower hc hY0 hY a b q η t W X V hWlo hXlo,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

end CubicFirstMoment

end

end OAI
