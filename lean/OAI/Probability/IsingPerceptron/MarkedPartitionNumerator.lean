import Mathlib
import OAI.Probability.IsingPerceptron.LintegralGammaKernel

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {E : Type} [MeasurableSpace E] [Nonempty E]

def markedPartitionNumerator (b l : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {d k : ℕ} (m : Fin d → ℝ) (F : Fin d → E → ℝ≥0∞) (z : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ ν, ENNReal.ofReal ((markedPoissonTotal ν).toReal ^ (l - ∑ i, m i)) *
    Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
      (fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) z ν
      ∂poissonLaw ((powerIntensity b).prod μ)

theorem markedPartitionNumerator_eq {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (z : Fin k → ℝ) (hl : l < ∑ i, m i) :
    markedPartitionNumerator b l μ m F z =
      (∏ i, ∫⁻ y, F i y ∂μ) * poissonPartitionNumerator b l m z := by
  have hw (i : Fin d) : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) :=
    (by fun_prop : Measurable (fun p : ℝ × E => ENNReal.ofReal ((max p.1 0)^(m i)))).mul
      ((hF i).comp measurable_snd)
  have hfac : Measurable (fun ν => Marked.poissonFactorial ((powerIntensity b).prod μ)
      Prod.fst d (fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) z ν) :=
    Marked.measurable_poissonFactorial_param _ measurable_fst d measurable_id measurable_const hw
  rw [markedPartitionNumerator, show l - ∑ i, m i = -((∑ i, m i)-l) by ring,
    expected_inverse_power _ measurable_markedPoissonTotal.ennreal_toReal hfac
      (markedPoissonTotal_positive hb hb1 μ) (sub_pos.mpr hl),
    poissonPartitionNumerator_eq hb hb1 m hm z hl]
  have hi (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        (∫⁻ ν, ENNReal.ofReal (Real.exp (-(t*(markedPoissonTotal ν).toReal))) *
          Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
            (fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) z ν
              ∂poissonLaw ((powerIntensity b).prod μ)) =
      ((∏ i, ∫⁻ y, F i y ∂μ) * ∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        (ENNReal.ofReal (t^((d : ℝ)*b-l-1)) *
          enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b)) := by
    have hae := (markedPoissonTotal_enegExp_ae hb hb1 μ ht).symm
    have heq := lintegral_congr_ae (hae.mul (ae_eq_refl (fun ν =>
      Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
        (fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) z ν)))
    simp only [Pi.mul_apply] at heq
    rw [heq, markedFactorial_power_laplace hb μ m hm F hF z ht]
    have hp : ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i)) =
        ENNReal.ofReal (t^((d : ℝ)*b-l-1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
      congr 2
      ring
    calc
      _ = ((∏ i, ∫⁻ y, F i y ∂μ) * ∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        ((ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
          ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i))) *
            enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b)) := by ring
      _ = _ := by rw [hp]
  rw [setLIntegral_congr_fun measurableSet_Ioi hi, lintegral_const_mul]
  · dsimp [partitionCoefficient, partitionTimeIntegral]
    ring
  · exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t^((d : ℝ)*b-l-1)))).mul
      (continuous_enegExp.measurable.comp (by fun_prop))

end IsingPerceptron

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma poissonLaw_ae_intensity (μ : Measure E) [SFinite μ] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν, p x := by
  have he : (∫⁻ ν, ν {x | ¬ p x} ∂poissonLaw μ) = 0 := by
    exact (poissonLaw_mean_count μ (show MeasurableSet {x | ¬p x} from hp.compl)).trans (ae_iff.mp h)
  have hz := (lintegral_eq_zero_iff (Measure.measurable_coe hp.compl)).mp he
  filter_upwards [hz] with ν hν
  exact ae_iff.mpr hν

def weightedPoissonTotal (a : E → ℝ≥0∞) (ν : Measure (ℝ × E)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (max p.1 0) * a p.2 ∂ν

omit [Nonempty E] in
lemma measurable_weightedPoissonTotal {a : E → ℝ≥0∞} (ha : Measurable a) :
    Measurable (weightedPoissonTotal a) :=
  Measure.measurable_lintegral ((by fun_prop : Measurable (fun p : ℝ × E => ENNReal.ofReal (max p.1 0))).mul
    (ha.comp measurable_snd))

lemma weightedPoissonTotal_real_eq_ae (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞) {t : ℝ} (ht : 0 ≤ t) :
    (fun ν => ∫⁻ p : ℝ × E, ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal) ∂ν) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal t * weightedPoissonTotal a ν) := by
  have hprod : ∀ᵐ p : ℝ × E ∂(powerIntensity b).prod μ, a p.2 < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt (ha.comp measurable_snd) measurable_const)).mpr
      (ae_of_all _ fun _ => hfin)
  filter_upwards [poissonLaw_ae_intensity ((powerIntensity b).prod μ)
    (measurableSet_lt (ha.comp measurable_snd) measurable_const) hprod] with ν hν
  rw [weightedPoissonTotal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hν] with p hp
  change a p.2 < ∞ at hp
  rw [ENNReal.ofReal_mul (mul_nonneg ht (le_max_right _ _)), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal hp.ne, mul_assoc]

omit [Nonempty E] in
lemma weightedPower_laplace_cost (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (1-Real.exp (-(t * max p.1 0 * (a p.2).toReal)))
      ∂(powerIntensity b).prod μ) =
      ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b := by
  rw [lintegral_prod_symm _ (by fun_prop)]
  have he : (fun y => ∫⁻ x, ENNReal.ofReal
      (1-Real.exp (-(t * max x 0 * (a y).toReal))) ∂powerIntensity b) =ᵐ[μ]
      (fun y => ENNReal.ofReal (t^b) * ENNReal.ofReal ((a y).toReal^b) * stableLaplaceConstant b) := by
    filter_upwards [hpos] with y hy
    have hmul (x : ℝ) : t * max x 0 * (a y).toReal = (t*(a y).toReal)*max x 0 := by ring
    simp_rw [hmul]
    have hs := powerIntensity_laplace_scale (b := b) (mul_pos ht hy)
    simp only [neg_mul] at hs ⊢
    rw [hs, Real.mul_rpow ht.le hy.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_congr_ae he, lintegral_mul_const _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

lemma weightedPoissonTotal_laplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      negExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := poissonLaw_laplace ((powerIntensity b).prod μ)
    (ψ := fun p => t * max p.1 0 * (a p.2).toReal) (by fun_prop)
    (fun p => mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) ENNReal.toReal_nonneg)
  rw [weightedPower_laplace_cost b μ ha hpos ht] at h
  rw [← h]
  apply integral_congr_ae
  exact ((weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp negExp).symm

end IsingPerceptron

namespace IsingPerceptron

structure RawTreeSpace where
  carrier : Type
  space : MeasurableSpace carrier

attribute [instance] RawTreeSpace.space

@[reducible] def rawTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, inferInstance⟩
  | n+1 => ⟨Measure (ℝ × (rawTreeSpace n).carrier), inferInstance⟩

abbrev RawTree (n : ℕ) := (rawTreeSpace n).carrier

instance rawTreeMeasurableSpace (n : ℕ) : MeasurableSpace (RawTree n) :=
  (rawTreeSpace n).space

instance rawTreeNonempty : (n : ℕ) → Nonempty (RawTree n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => ⟨(0 : Measure (ℝ × RawTree n))⟩

def rawTreeTotal : (n : ℕ) → RawTree n → ℝ≥0∞
  | 0, _ => 1
  | n+1, ν => ∫⁻ p : ℝ × RawTree n, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2 ∂ν

lemma measurable_rawTreeTotal (n : ℕ) : Measurable (rawTreeTotal n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_lintegral
      ((by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        (ih.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron

def rawCascadeLaw : (n : ℕ) → (ℕ → ℝ) → ProbabilityMeasure (RawTree n)
  | 0, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, b => ⟨poissonLaw ((powerIntensity (b 0)).prod
      (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))), by
        change IsProbabilityMeasure (poissonLaw ((powerIntensity (b 0)).prod
          (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))))
        exact poissonLaw_probability _⟩

lemma rawCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) :
    (rawCascadeLaw (n+1) b : Measure (RawTree (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod
        (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))) := rfl

lemma rawTreeTotal_succ (n : ℕ) (ν : RawTree (n+1)) :
    rawTreeTotal (n+1) ν = weightedPoissonTotal (rawTreeTotal n) ν := rfl

def HasStableTotal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ≥0∞) (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
    (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C*t^b)

lemma HasStableTotal.finite_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  obtain ⟨C, hC, hl⟩ := h
  exact stable_laplace_finite_positive P hX hC hb hl

lemma HasStableTotal.real_laplace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-t * (X ω).toReal) ∂P) = Real.exp (-C*t^b) := by
  have hf := h.finite_positive hX hb
  obtain ⟨C, hC, hl⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [← hl t ht]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]

lemma HasStableTotal.positive_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) : Integrable (fun ω => (X ω).toReal^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  exact stable_positive_moment P hX.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hC hr hrb hl

lemma HasStableTotal.negative_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) : Integrable (fun ω => ((X ω).toReal)⁻¹^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  apply stable_negative_moment P hX.ennreal_toReal _ hC hb hr hl
  filter_upwards [h.finite_positive hX hb] with ω hω
  exact ENNReal.toReal_pos hω.1.ne' hω.2.ne

lemma weightedPoissonTotal_stable {E : Type*} [MeasurableSpace E] [Nonempty E]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) :
    HasStableTotal (poissonLaw ((powerIntensity b).prod μ)) (weightedPoissonTotal a) b := by
  let A := ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ
  have hA : A < ∞ := by
    exact hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
      |>.mp hpay.hasFiniteIntegral
  have hApos : 0 < A := by
    apply (lintegral_pos_iff_support (ha.ennreal_toReal.pow_const b |>.ennreal_ofReal)).mpr
    have he : (Function.support (fun y => ENNReal.ofReal ((a y).toReal^b))) =ᵐ[μ] Set.univ := by
      filter_upwards [hpos] with y hy
      apply propext
      change (ENNReal.ofReal ((a y).toReal^b) ≠ 0) ↔ True
      exact iff_true_intro (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)))
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let C := A * stableLaplaceConstant b
  have hC : C < ∞ := ENNReal.mul_lt_top hA (stableLaplaceConstant_lt_top hb hb1)
  have hCp : 0 < C := ENNReal.mul_pos hApos.ne' (stableLaplaceConstant_pos hb).ne'
  refine ⟨C.toReal, ENNReal.toReal_pos hCp.ne' hC.ne, fun t ht => ?_⟩
  rw [weightedPoissonTotal_laplace b μ ha hfin hpos ht, mul_assoc]
  change negExp (ENNReal.ofReal (t^b) * C) = _
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

def CascadeExponents (n : ℕ) (b : ℕ → ℝ) : Prop :=
  (∀ i < n, 0 < b i ∧ b i < 1) ∧ ∀ i j, i < j → j < n → b i < b j

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

theorem rawCascade_total_moments (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    (∀ᵐ T ∂(rawCascadeLaw n b : Measure (RawTree n)),
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) ∧
    (∀ r : ℝ, 0 < r → (∀ i < n, r < b i) →
      Integrable (fun T => (rawTreeTotal n T).toReal^r) (rawCascadeLaw n b : Measure (RawTree n))) ∧
    (∀ r : ℝ, 0 < r → Integrable (fun T => ((rawTreeTotal n T).toReal)⁻¹^r)
      (rawCascadeLaw n b : Measure (RawTree n))) := by
  induction n generalizing b with
  | zero =>
    refine ⟨ae_of_all _ (fun _ => by simp [rawTreeTotal]), ?_, ?_⟩
    · intro r _ _
      simp [rawTreeTotal]
    · intro r _
      simp [rawTreeTotal]
  | succ n ih =>
    have hi := ih (fun i => b (i+1)) hb.tail
    have hb0 := hb.1 0 (by omega)
    have hpos : ∀ᵐ T ∂(rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n)),
        0 < (rawTreeTotal n T).toReal := by
      filter_upwards [hi.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    have hm := hi.2.1 (b 0) hb0.1 (fun i hi => hb.2 0 (i+1) (by omega) (by omega))
    have hs : HasStableTotal (rawCascadeLaw (n+1) b : Measure (RawTree (n+1)))
        (rawTreeTotal (n+1)) (b 0) :=
      weightedPoissonTotal_stable hb0.1 hb0.2 _ (measurable_rawTreeTotal n)
        (hi.1.mono fun _ h => h.2) hpos hm
    exact ⟨hs.finite_positive (measurable_rawTreeTotal _) hb0.1,
      fun r hr hrb => hs.positive_moment (measurable_rawTreeTotal _) hb0.1 hr (hrb 0 (by omega)),
      fun r hr => hs.negative_moment (measurable_rawTreeTotal _) hb0.1 hr⟩

theorem rawCascade_total_log_square (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    Integrable (fun T => (Real.log (rawTreeTotal n T).toReal)^2)
      (rawCascadeLaw n b : Measure (RawTree n)) := by
  cases n with
  | zero => simp [rawTreeTotal]
  | succ n =>
    have h := rawCascade_total_moments (n+1) b hb
    have hb0 := hb.1 0 (by omega)
    apply integrable_log_sq_of_moments _ (measurable_rawTreeTotal _).ennreal_toReal _
      (show 0 < b 0/2 by linarith) (h.2.1 _ (by linarith) _) (h.2.2 _ (by linarith))
    · filter_upwards [h.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    · intro i hi
      by_cases h0 : i = 0
      · subst i; linarith
      · have := hb.2 0 i (by omega) hi; linarith

open scoped ProbabilityTheory

lemma measurable_withDensity_fixed {E : Type*} [MeasurableSpace E]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun ν : Measure E => ν.withDensity f) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [withDensity_apply _ hs, ← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hf.indicator hs)

def normalizeMass {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) : Measure E :=
  if 0 < ν univ ∧ ν univ < ∞ then (ν univ)⁻¹ • ν
  else Measure.dirac (Classical.choice (inferInstance : Nonempty E))

lemma measurable_normalizeMass {E : Type*} [MeasurableSpace E] [Nonempty E] :
    Measurable (normalizeMass : Measure E → Measure E) := by
  have hm : Measurable (fun ν : Measure E => ν univ) := Measure.measurable_coe MeasurableSet.univ
  apply Measurable.ite ((measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const))
  · apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hm.inv.mul (Measure.measurable_coe hs)
  · exact measurable_const

instance normalizeMass_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) : IsProbabilityMeasure (normalizeMass ν) := by
  unfold normalizeMass
  split_ifs with h
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h.1.ne' h.2.ne
  · infer_instance

def childMass (n : ℕ) (ν : RawTree (n+1)) : Measure (ℝ × RawTree n) :=
  ν.withDensity (fun p => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2)

lemma childMass_univ (n : ℕ) (ν : RawTree (n+1)) :
    childMass n ν univ = rawTreeTotal (n+1) ν := by
  simp [childMass, withDensity_apply, rawTreeTotal]

lemma measurable_childMass (n : ℕ) : Measurable (childMass n) :=
  measurable_withDensity_fixed
    ((by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd))

def rawChildKernel (n : ℕ) : Kernel (RawTree (n+1)) (ℝ × RawTree n) :=
  ⟨fun ν => normalizeMass (childMass n ν), measurable_normalizeMass.comp (measurable_childMass n)⟩

instance rawChildKernel_markov (n : ℕ) : IsMarkovKernel (rawChildKernel n) :=
  ⟨fun _ => normalizeMass_probability _⟩

@[reducible] def RawLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ℝ × RawLeaf n

instance rawLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (RawLeaf n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := rawLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ℝ × RawLeaf n))

instance rawLeafNonempty : (n : ℕ) → Nonempty (RawLeaf n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := rawLeafNonempty n
    inferInstanceAs (Nonempty (ℝ × RawLeaf n))

def rawLeafKernelData : (n : ℕ) → {κ : Kernel (RawTree n) (RawLeaf n) // IsMarkovKernel κ}
  | 0 => ⟨Kernel.const _ (Measure.dirac PUnit.unit), by
      change IsMarkovKernel (Kernel.const PUnit (Measure.dirac (PUnit.unit : PUnit)))
      infer_instance⟩
  | n+1 =>
    let κ := (rawLeafKernelData n).val
    letI : IsMarkovKernel κ := (rawLeafKernelData n).property
    ⟨((Kernel.id : Kernel ℝ ℝ) ∥ₖ κ) ∘ₖ rawChildKernel n, by
      change IsMarkovKernel (((Kernel.id : Kernel ℝ ℝ) ∥ₖ κ) ∘ₖ rawChildKernel n)
      infer_instance⟩

def rawLeafKernel (n : ℕ) : Kernel (RawTree n) (RawLeaf n) := (rawLeafKernelData n).val

instance rawLeafKernel_markov (n : ℕ) : IsMarkovKernel (rawLeafKernel n) :=
  (rawLeafKernelData n).property

lemma rawLeafKernel_succ (n : ℕ) :
    rawLeafKernel (n+1) = ((Kernel.id : Kernel ℝ ℝ) ∥ₖ rawLeafKernel n) ∘ₖ rawChildKernel n := rfl

lemma rawChildKernel_lintegral (n : ℕ) (ν : RawTree (n+1))
    (hν : 0 < rawTreeTotal (n+1) ν ∧ rawTreeTotal (n+1) ν < ∞)
    {F : ℝ × RawTree n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂rawChildKernel n ν) = (rawTreeTotal (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (childMass n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [childMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, childMass_univ, childMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2) from
      ((by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd))) hF

lemma rawLeafKernel_lintegral (n : ℕ) (ν : RawTree (n+1))
    (hν : 0 < rawTreeTotal (n+1) ν ∧ rawTreeTotal (n+1) ν < ∞)
    {F : RawLeaf (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂rawLeafKernel (n+1) ν) = (rawTreeTotal (n+1) ν)⁻¹ *
      ∫⁻ p : ℝ × RawTree n, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2 *
        (∫⁻ v, F (p.1,v) ∂rawLeafKernel n p.2) ∂ν := by
  rw [rawLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  have he : (fun p : ℝ × RawTree n => ∫⁻ v, F v ∂((Kernel.id : Kernel ℝ ℝ) ∥ₖ rawLeafKernel n) p) =
      (fun p : ℝ × RawTree n => ∫⁻ v, F (p.1,v) ∂rawLeafKernel n p.2) := by
    funext p
    rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
      lintegral_dirac']
    exact hF.lintegral_prod_right'
  rw [rawChildKernel_lintegral n ν hν (hF.lintegral_kernel)]
  apply congrArg ((rawTreeTotal (n+1) ν)⁻¹ * ·)
  apply lintegral_congr
  intro p
  rw [congrFun he p]

end IsingPerceptron

namespace IsingPerceptron
variable {E : Type} [MeasurableSpace E] [Nonempty E]

lemma weightedPoissonTotal_enlaplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      enegExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := congrArg ENNReal.ofReal (weightedPoissonTotal_laplace b μ ha hfin hpos ht)
  have hi : Integrable (fun ν => negExp (ENNReal.ofReal t * weightedPoissonTotal a ν))
      (poissonLaw ((powerIntensity b).prod μ)) :=
    integrable_negExp _ (measurable_const.mul (measurable_weightedPoissonTotal ha))
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => negExp_nonneg _)] at h
  simpa only [negExp, ENNReal.ofReal_toReal (enegExp_ne_top _)] using h

omit [Nonempty E] in
lemma weighted_power_moment_laplace {b m t : ℝ} (hb : 0 < b) (hmb : b < m)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {F : E → ℝ≥0∞}
    (hF : Measurable F) (ht : 0 < t) :
    (∫⁻ p : ℝ × E, (ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^m) * F p.2) *
      enegExp (ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal)) ∂(powerIntensity b).prod μ) =
      (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F y ∂μ) *
        ENNReal.ofReal (b * Real.Gamma (m-b)) * ENNReal.ofReal (t^(b-m)) := by
  have hmeas : Measurable (fun p : ℝ × E =>
      (ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^m) * F p.2) *
        enegExp (ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal))) :=
    ((by fun_prop : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^m))).mul (hF.comp measurable_snd)).mul
        (continuous_enegExp.measurable.comp (by fun_prop))
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hi : (fun y => ∫⁻ x, (ENNReal.ofReal ((max x 0 * (a y).toReal)^m) * F y) *
      enegExp (ENNReal.ofReal (t * max x 0 * (a y).toReal)) ∂powerIntensity b) =ᵐ[μ]
      (fun y => (ENNReal.ofReal ((a y).toReal^b) * F y) *
        ENNReal.ofReal (b * Real.Gamma (m-b)) * ENNReal.ofReal (t^(b-m))) := by
    filter_upwards [hpos] with y hy
    have hx (x : ℝ) : (ENNReal.ofReal ((max x 0 * (a y).toReal)^m) * F y) *
        enegExp (ENNReal.ofReal (t * max x 0 * (a y).toReal)) =
        (ENNReal.ofReal ((a y).toReal^m) * F y) *
          (ENNReal.ofReal ((max x 0)^m) * ENNReal.ofReal (Real.exp (-(t*(a y).toReal) * max x 0))) := by
      rw [Real.mul_rpow (le_max_right _ _) hy.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (le_max_right _ _) _),
        enegExp_ofReal (mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) hy.le)]
      have hh : -(t * max x 0 * (a y).toReal) = -(t*(a y).toReal) * max x 0 := by ring
      rw [hh]
      ring
    simp_rw [hx]
    rw [lintegral_const_mul _ (by fun_prop), powerIntensity_moment_laplace hb hmb (mul_pos ht hy),
      ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hmb)).le),
      Real.mul_rpow ht.le hy.le, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    have hp : ENNReal.ofReal ((a y).toReal^m) * ENNReal.ofReal ((a y).toReal^(b-m)) =
        ENNReal.ofReal ((a y).toReal^b) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _), ← Real.rpow_add hy,
        show m + (b-m) = b by ring]
    calc
      _ = ((ENNReal.ofReal ((a y).toReal^m) * ENNReal.ofReal ((a y).toReal^(b-m))) * F y) *
          ENNReal.ofReal (b * Real.Gamma (m-b)) * ENNReal.ofReal (t^(b-m)) := by ring
      _ = _ := by rw [hp]
  rw [lintegral_congr_ae hi, lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop)]

lemma weightedFactorial_power_laplace {b : ℝ} (hb : 0 < b)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hfin : ∀ᵐ y ∂μ, a y < ∞) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (z : Fin k → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * weightedPoissonTotal a ν) *
      Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
        (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν
      ∂poissonLaw ((powerIntensity b).prod μ)) =
    ((∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ) *
      (∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b)))) *
      ENNReal.ofReal (t ^ ((d : ℝ)*b - ∑ i, m i)) *
        enegExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
          stableLaplaceConstant b) := by
  have h := Marked.poissonFactorial_laplace ((powerIntensity b).prod μ)
    measurable_fst (markedPower_fiber_null b μ) d
    (w := fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2)
    (fun i => (by fun_prop : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)))).mul ((hF i).comp measurable_snd))
    (ψ := fun p => ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal)) (by fun_prop) z
  have he := (weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp enegExp
  have he' := lintegral_congr_ae he
  have he'' := lintegral_congr_ae (he.mul (ae_eq_refl (fun ν =>
      Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
        (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν)))
  simp only [Pi.mul_apply, Function.comp_apply] at he' he''
  simp only [Marked.poissonLaplaceWeight] at h
  rw [← he'', h, he', weightedPoissonTotal_enlaplace b μ ha hfin hpos ht]
  have hi (i : Fin d) := weighted_power_moment_laplace hb (hm i) μ ha hpos (hF i) ht
  simp_rw [hi, Finset.prod_mul_distrib]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg ht.le (b-m i)),
    ← Real.rpow_sum_of_pos ht]
  congr 3
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma weightedPoissonTotal_enegExp_ae {b t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hfin : ∀ᵐ y ∂μ, a y < ∞) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) (ht : 0 < t) :
    (fun ν => enegExp (ENNReal.ofReal t * weightedPoissonTotal a ν)) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal (Real.exp (-(t*(weightedPoissonTotal a ν).toReal)))) := by
  filter_upwards [(weightedPoissonTotal_stable hb hb1 μ ha hfin hpos hpay).finite_positive
    (measurable_weightedPoissonTotal ha) hb] with ν hν
  rw [← ENNReal.ofReal_toReal hν.2.ne, ← ENNReal.ofReal_mul ht.le,
    enegExp_ofReal (mul_nonneg ht.le ENNReal.toReal_nonneg)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

def weightedPartitionNumerator (b l : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (a : E → ℝ≥0∞) {d k : ℕ} (m : Fin d → ℝ) (F : Fin d → E → ℝ≥0∞)
    (z : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ ν, ENNReal.ofReal ((weightedPoissonTotal a ν).toReal ^ (l - ∑ i, m i)) *
    Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
      (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν
      ∂poissonLaw ((powerIntensity b).prod μ)

def weightedPartitionTimeIntegral (b l : ℝ) (d : ℕ) (A : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^((d : ℝ)*b-l-1)) *
    enegExp (ENNReal.ofReal (t^b) * A * stableLaplaceConstant b)

theorem weightedPartitionNumerator_eq {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hfin : ∀ᵐ y ∂μ, a y < ∞) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (z : Fin k → ℝ) (hl : l < ∑ i, m i) :
    weightedPartitionNumerator b l μ a m F z =
      (∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ) *
        partitionCoefficient b l m * weightedPartitionTimeIntegral b l d
          (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) := by
  have hw (i : Fin d) : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) :=
    (by fun_prop : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)))).mul ((hF i).comp measurable_snd)
  have hfac : Measurable (fun ν => Marked.poissonFactorial ((powerIntensity b).prod μ)
      Prod.fst d (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν) :=
    Marked.measurable_poissonFactorial_param _ measurable_fst d measurable_id measurable_const hw
  have hp : ∀ᵐ ν ∂poissonLaw ((powerIntensity b).prod μ),
      0 < (weightedPoissonTotal a ν).toReal := by
    filter_upwards [(weightedPoissonTotal_stable hb hb1 μ ha hfin hpos hpay).finite_positive
      (measurable_weightedPoissonTotal ha) hb] with ν hν
    exact ENNReal.toReal_pos hν.1.ne' hν.2.ne
  rw [weightedPartitionNumerator, show l - ∑ i, m i = -((∑ i, m i)-l) by ring,
    expected_inverse_power _ (measurable_weightedPoissonTotal ha).ennreal_toReal hfac hp (sub_pos.mpr hl)]
  have hi (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        (∫⁻ ν, ENNReal.ofReal (Real.exp (-(t*(weightedPoissonTotal a ν).toReal))) *
          Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
            (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν
              ∂poissonLaw ((powerIntensity b).prod μ)) =
      ((∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ) *
          ∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        (ENNReal.ofReal (t^((d : ℝ)*b-l-1)) *
          enegExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
            stableLaplaceConstant b)) := by
    have hae := (weightedPoissonTotal_enegExp_ae hb hb1 μ ha hfin hpos hpay ht).symm
    have heq := lintegral_congr_ae (hae.mul (ae_eq_refl (fun ν =>
      Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
        (fun i p => ENNReal.ofReal ((max p.1 0 * (a p.2).toReal)^(m i)) * F i p.2) z ν)))
    simp only [Pi.mul_apply] at heq
    rw [heq, weightedFactorial_power_laplace hb μ ha hfin hpos m hm F hF z ht]
    have he : ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i)) =
        ENNReal.ofReal (t^((d : ℝ)*b-l-1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
      congr 2
      ring
    calc
      _ = ((∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ) *
          ∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        ((ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
          ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i))) *
            enegExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
              stableLaplaceConstant b)) := by ring
      _ = _ := by rw [he]
  rw [setLIntegral_congr_fun measurableSet_Ioi hi, lintegral_const_mul]
  · dsimp [partitionCoefficient, weightedPartitionTimeIntegral]
    ring
  · exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t^((d : ℝ)*b-l-1)))).mul
      (continuous_enegExp.measurable.comp (by fun_prop))

end IsingPerceptron

end

end OAI
