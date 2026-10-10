import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Scaling
import OAI.Probability.GaussianInformation.Kernel.GaussianRows

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

abbrev Mat (p d : ℕ) := Fin p → Fin d → ℝ
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def applyRows {p d : ℕ} (X : Mat p d) (s : Vec d) : Fin p → ℝ :=
  fun i => ∑ j,X i j*s j

lemma applyRows_sub {p d : ℕ} (X : Mat p d) (s u : Vec d) :
    applyRows X (s-u)=applyRows X s-applyRows X u := by
  ext i
  simp [applyRows,mul_sub,Finset.sum_sub_distrib]

lemma continuous_applyRows {p d : ℕ} :
    Continuous (fun t : Mat p d × Vec d => applyRows t.1 t.2) := by
  unfold applyRows
  fun_prop

noncomputable def atDensity {p d : ℕ} (r : ℝ) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) : ℝ :=
  labelDensity r (y-applyRows X u)

lemma atDensity_pos {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) :
    0 < atDensity r X y u := labelDensity_pos hr _

lemma continuous_atDensity {p d : ℕ} (r : ℝ) :
    Continuous (fun t : (Mat p d × (Fin p → ℝ)) × Vec d => atDensity r t.1.1 t.1.2 t.2) := by
  unfold atDensity labelDensity gaussianPDFReal applyRows
  fun_prop

lemma continuous_log_atDensity {p d : ℕ} {r : ℝ} (hr : 0 < r) :
    Continuous (fun t : (Mat p d × (Fin p → ℝ)) × Vec d => Real.log (atDensity r t.1.1 t.1.2 t.2)) :=
  (continuous_atDensity r).log (fun t => (atDensity_pos hr t.1.1 t.1.2 t.2).ne')

noncomputable def densityBound (p : ℕ) (r : ℝ) : ℝ := (Real.sqrt (2*Real.pi*r^2))⁻¹^p
lemma densityBound_pos (p : ℕ) {r : ℝ} (hr : 0 < r) : 0 < densityBound p r := by
  unfold densityBound; positivity

lemma atDensity_le {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) :
    atDensity r X y u ≤ densityBound p r := by
  unfold atDensity labelDensity
  calc
    _ ≤ ∏ _i : Fin p,(Real.sqrt (2*Real.pi*r^2))⁻¹ := by
      apply Finset.prod_le_prod₀ (fun _ _ => gaussianPDFReal_nonneg _ _ _)
      intro i _
      unfold gaussianPDFReal
      simp only [NNReal.coe_mk]
      calc
        _ ≤ (Real.sqrt (2*Real.pi*r^2))⁻¹*1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [sq_nonneg ((y-applyRows X u) i)]) (by positivity))
        _ = _ := mul_one _
    _ = _ := by simp [densityBound]

lemma integrable_atDensity {p d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) :
    Integrable (atDensity r X y) ν := by
  have hm : Measurable (atDensity r X y) := by
    unfold atDensity labelDensity gaussianPDFReal applyRows
    fun_prop
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := densityBound p r) ?_⟩
  exact (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs,abs_of_pos (atDensity_pos hr X y u)]
      exact atDensity_le hr X y u))

lemma integral_atDensity_pos {p d : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) :
    0 < ∫ u,atDensity r X y u ∂ν := by
  apply (integral_pos_iff_support_of_nonneg (fun u => (atDensity_pos hr X y u).le)
    (integrable_atDensity ν hr X y)).mpr
  have he : Function.support (atDensity r X y)=univ := by
    ext u; simp [Function.mem_support,(atDensity_pos hr X y u).ne']
  rw [he,measure_univ]
  norm_num

lemma integral_density_y {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (u : Vec d) :
    (∫ y : Fin p → ℝ,atDensity r X y u)=1 := by
  have hv : (NNReal.mk (r^2) (sq_nonneg r)) ≠ 0 := by
    intro h; have hh := congrArg (fun t : NNReal => (t:ℝ)) h
    exact (pow_ne_zero 2 hr.ne') hh
  have he (y : Fin p → ℝ) : atDensity r X y u =
      ∏ i,gaussianPDFReal (applyRows X u i) (NNReal.mk (r^2) (sq_nonneg r)) (y i) := by
    unfold atDensity labelDensity gaussianPDFReal
    simp
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one _ hv]

lemma lintegral_density_y {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (u : Vec d) :
    (∫⁻ y : Fin p → ℝ,ENNReal.ofReal (atDensity r X y u))=1 := by
  have hi : Integrable (fun y : Fin p → ℝ => atDensity r X y u) volume :=
    Integrable.of_integral_ne_zero (by rw [integral_density_y hr X u]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => (atDensity_pos hr _ _ _).le)),
    integral_density_y hr X u,ENNReal.ofReal_one]

noncomputable def mixture {p d L : ℕ} (ν : Measure (Vec d)) (r : Fin L → ℝ)
    (X : Mat p d) (y : Fin p → ℝ) : ℝ :=
  (L:ℝ)⁻¹*∑ j,∫ u,atDensity (r j) X y u ∂ν

lemma measurable_mixture {p d L : ℕ} (ν : Measure (Vec d)) [SFinite ν] (r : Fin L → ℝ) :
    Measurable (fun t : Mat p d × (Fin p → ℝ) => mixture ν r t.1 t.2) := by
  unfold mixture
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro j _
  exact (continuous_atDensity (p := p) (d := d) (r j)).stronglyMeasurable.integral_prod_right.measurable

lemma mixture_nonneg {p d L : ℕ} (ν : Measure (Vec d)) (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) :
    0 ≤ mixture ν r X y := by
  unfold mixture
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun u => (atDensity_pos (hr j) _ _ _).le))

lemma mixture_lower {p d L : ℕ} (ν : Measure (Vec d)) (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) (j : Fin L) :
    (∫ u,atDensity (r j) X y u ∂ν)/(L:ℝ) ≤ mixture ν r X y := by
  unfold mixture
  rw [div_eq_mul_inv,mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.single_le_sum (fun i _ => integral_nonneg (fun u => (atDensity_pos (hr i) X y u).le)) (Finset.mem_univ j)

lemma mixture_pos {p d L : ℕ} (hL : 0 < L) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) :
    0 < mixture ν r X y :=
  lt_of_lt_of_le (div_pos (integral_atDensity_pos ν (hr ⟨0,hL⟩) X y) (by positivity))
    (mixture_lower ν r hr X y ⟨0,hL⟩)

lemma lintegral_mixture {p d L : ℕ} (hL : 0 < L) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) :
    (∫⁻ y : Fin p → ℝ,ENNReal.ofReal (mixture ν r X y))=1 := by
  have he (y : Fin p → ℝ) : ENNReal.ofReal (mixture ν r X y)=
      (L:ℝ≥0∞)⁻¹*∑ j,∫⁻ u,ENNReal.ofReal (atDensity (r j) X y u) ∂ν := by
    unfold mixture
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1; apply Finset.sum_congr rfl; intro j _
      exact ofReal_integral_eq_lintegral_ofReal (integrable_atDensity ν (hr j) X y)
        (Filter.Eventually.of_forall (fun u => (atDensity_pos (hr j) _ _ _).le))
    · intro j _; exact integral_nonneg (fun u => (atDensity_pos (hr j) _ _ _).le)
  simp_rw [he]
  rw [lintegral_const_mul]
  · rw [lintegral_finsetSum]
    · have hj (j : Fin L) : (∫⁻ y : Fin p → ℝ,∫⁻ u,ENNReal.ofReal (atDensity (r j) X y u) ∂ν)=1 := by
        rw [lintegral_lintegral_swap]
        · simp only [lintegral_density_y (hr j) X,lintegral_one,measure_univ]
        · exact ((continuous_atDensity (r j)).measurable.comp
            ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal.aemeasurable
      simp_rw [hj]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hL.ne') (by simp)
    · intro j _
      apply Measurable.lintegral_prod_right
      exact ((continuous_atDensity (r j)).measurable.comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  · apply Finset.measurable_fun_sum; intro j _
    apply Measurable.lintegral_prod_right
    exact ((continuous_atDensity (r j)).measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal

end ReferenceGaussian

end OAI
