import Mathlib
import OAI.Probability.Ballisticity.Walk.TailGrowth

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]

noncomputable def cutKernel (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) : Kernel D X where
  toFun d := (w d (S (j d)))⁻¹ • (w d).restrict (S (j d))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have h₁ : Measurable (fun p : D × ℤ => w p.1 (S p.2)) :=
      measurable_from_prod_countable_left fun n => w.measurable_coe (hS n)
    have h₂ : Measurable (fun p : D × ℤ => w p.1 (A ∩ S p.2)) :=
      measurable_from_prod_countable_left fun n => w.measurable_coe (hA.inter (hS n))
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
    exact (h₁.comp (measurable_id.prodMk hj)).inv.mul
      (h₂.comp (measurable_id.prodMk hj))

lemma cutKernel_apply (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) (d : D) :
    cutKernel w S hS j hj d = (w d (S (j d)))⁻¹ • (w d).restrict (S (j d)) := rfl

lemma cutKernel_markov (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j)
    (hpos : ∀ d, w d (S (j d)) ≠ 0) (hfin : ∀ d, w d (S (j d)) ≠ ∞) :
    IsMarkovKernel (cutKernel w S hS j hj) := by
  constructor
  intro d
  constructor
  simp only [cutKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel (hpos d) (hfin d)

lemma cutKernel_supported (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂cutKernel w S hS j hj d, x ∈ S (j d) := by
  exact Measure.ae_smul_measure (ae_restrict_mem (hS (j d))) _

lemma cutKernel_mass_mul (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j)
    (d : D) (hpos : w d (S (j d)) ≠ 0) (hfin : w d (S (j d)) ≠ ∞) :
    w d (S (j d)) • cutKernel w S hS j hj d = (w d).restrict (S (j d)) := by
  rw [cutKernel_apply, smul_smul, ENNReal.mul_inv_cancel hpos hfin, one_smul]

lemma coordinate_atom_pos (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSingletonClass X] (ξ : X → ℤ) (hξ : Measurable ξ)
    (hsurj : Function.Surjective ξ) (hμ : ∀ x, 0 < μ.real {x}) (z : ℤ) :
    0 < (μ.map ξ).real {z} := by
  obtain ⟨x,hx⟩ := hsurj z
  rw [Measure.real, Measure.map_apply hξ (measurableSet_singleton z)]
  apply lt_of_lt_of_le (hμ x)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  subst y
  exact hx

end TailSampling

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TailGrowth

lemma log_integral_lower_of_exp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (Z p : X → ℝ) (a : ℝ)
    (hZ : Integrable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    (hp : Integrable p μ) (hlower : ∀ᵐ x ∂μ, Real.exp (-a - Z x) ≤ p x) :
    0 < ∫ x, p x ∂μ ∧
      -a - (∫ x, Z x ∂μ) ≤ Real.log (∫ x, p x ∂μ) := by
  have hF : Integrable (fun x => -a - Z x) μ := (integrable_const (-a)).sub hZ
  have hE : Integrable (fun x => Real.exp (-a - Z x)) μ := by
    apply (integrable_const (Real.exp (-a))).mono' (Real.continuous_exp.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    filter_upwards [hZ0] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    hF hE
  have hi : (∫ x, -a - Z x ∂μ) = -a - ∫ x, Z x ∂μ := by
    rw [integral_sub (integrable_const _) hZ, integral_const]
    simp
  rw [hi] at hj
  have hb := hj.trans (integral_mono_ae hE hp hlower)
  have hp0 := (Real.exp_pos _).trans_le hb
  refine ⟨hp0, ?_⟩
  calc
    -a - (∫ x, Z x ∂μ) = Real.log (Real.exp (-a - ∫ x, Z x ∂μ)) :=
      (Real.log_exp _).symm
    _ ≤ Real.log (∫ x, p x ∂μ) := Real.log_le_log (Real.exp_pos _) hb

lemma log_integral_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (Z p : X → ℝ) (a : ℝ)
    (hZ : Integrable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    (hp : Integrable p μ) (hp0 : ∀ᵐ x ∂μ, 0 < p x)
    (hlower : ∀ᵐ x ∂μ, -a - Z x ≤ Real.log (p x)) :
    0 < ∫ x, p x ∂μ ∧
      -a - (∫ x, Z x ∂μ) ≤ Real.log (∫ x, p x ∂μ) := by
  apply log_integral_lower_of_exp μ Z p a hZ hZ0 hp
  filter_upwards [hp0,hlower] with x hx h
  simpa only [Real.exp_log hx] using Real.exp_le_exp.mpr h

end TailGrowth

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailGrowth

lemma measurable_statistic {D : Type*} [MeasurableSpace D] (w : Kernel D ℤ) (R : ℤ) :
    Measurable (fun d => statistic (w d) R) := by
  apply Measurable.iSup
  intro j
  exact ((w.measurable_coe (s := Set.Iic j) measurableSet_Iic).ennreal_toReal).min
    ((w.measurable_coe (s := Set.Ici (j+R)) measurableSet_Ici).ennreal_toReal)

lemma statistic_translate (μ : Measure ℤ) (R z : ℤ) :
    statistic (μ.map (fun x => x+z)) R = statistic μ R := by
  unfold statistic
  have he (j : ℤ) : TailCuts.score (TailCuts.lower (μ.map (fun x => x+z)))
      (TailCuts.upper (μ.map (fun x => x+z))) R j =
      TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R (j-z) := by
    unfold TailCuts.score TailCuts.lower TailCuts.upper Measure.real
    rw [Measure.map_apply (show Measurable (fun x : ℤ => x+z) from measurable_of_countable _) measurableSet_Iic,
      Measure.map_apply (show Measurable (fun x : ℤ => x+z) from measurable_of_countable _) measurableSet_Ici]
    congr 3
    · ext x
      simp only [Set.mem_preimage, Set.mem_Iic]
      omega
    · ext x
      simp only [Set.mem_preimage, Set.mem_Ici]
      omega
  simp_rw [he]
  exact (show Function.Surjective (fun j : ℤ => j-z) from
    fun j => ⟨j+z,by dsimp; omega⟩).iSup_comp _

lemma comp_mono_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) {μ ν : Measure X} (h : μ ≤ ν) :
    κ ∘ₘ μ ≤ κ ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.bind_apply hs κ.measurable.aemeasurable,
    Measure.bind_apply hs κ.measurable.aemeasurable]
  exact lintegral_mono' h le_rfl

lemma smul_mono_scalar {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {a b : ℝ≥0∞} (h : a ≤ b) : a • μ ≤ b • μ := by
  apply Measure.le_iff.mpr
  intro s _
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul h le_rfl zero_le zero_le

lemma normalized_tail_dominated {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X)
    (hpos : μ s ≠ 0) {t : ℝ} (ht : t ≤ μ.real s) :
    ENNReal.ofReal t • ((μ s)⁻¹ • μ.restrict s) ≤ μ := by
  have hh : ENNReal.ofReal t ≤ μ s :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr ht
  calc
    ENNReal.ofReal t • ((μ s)⁻¹ • μ.restrict s) ≤
        μ s • ((μ s)⁻¹ • μ.restrict s) := smul_mono_scalar _ hh
    _ = μ.restrict s := by
      rw [smul_smul, ENNReal.mul_inv_cancel hpos (measure_ne_top _ _), one_smul]
    _ ≤ μ := Measure.restrict_le_self

lemma continued_tail_dominated {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) (w : Measure X) [IsFiniteMeasure w] (w' : Measure Y)
    (s : Set X) (hpos : w s ≠ 0) {C t : ℝ} (ht : t ≤ w.real s)
    (hupdate : ENNReal.ofReal (Real.exp C) • (κ ∘ₘ w) ≤ w') :
    ENNReal.ofReal (Real.exp C * t) •
      (κ ∘ₘ ((w s)⁻¹ • w.restrict s)) ≤ w' := by
  have hh := comp_mono_left κ (normalized_tail_dominated w s hpos ht)
  rw [Measure.comp_smul] at hh
  have hh' := smul_le_smul_left (ENNReal.ofReal (Real.exp C)) hh
  rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos C).le] at hh'
  exact hh'.trans hupdate

lemma stream_real_lower {X : Type*} [MeasurableSpace X]
    (μ w' : Measure X) [IsFiniteMeasure w'] {t : ℝ} (ht : 0 ≤ t)
    (h : ENNReal.ofReal t • μ ≤ w') (s : Set X) : t * μ.real s ≤ w'.real s := by
  have hh := ENNReal.toReal_mono (measure_ne_top w' s) (h s)
  simpa only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht] using hh

lemma prod_comp {X X' Y Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']
    (κ : Kernel X Y) (η : Kernel X' Y') [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (μ : Measure X) (ν : Measure X') [SFinite μ] [SFinite ν] :
    (κ ∘ₘ μ).prod (η ∘ₘ ν) = (κ ∥ₖ η) ∘ₘ (μ.prod ν) := by
  have hh := congrArg (fun K : Kernel (Unit × Unit) (Y × Y') => K ((),()))
    (Kernel.parallelComp_comp_parallelComp
      (κ := Kernel.const Unit μ) (κ' := Kernel.const Unit ν) (η := κ) (η' := η))
  simpa only [Kernel.comp_apply,Kernel.parallelComp_apply,Kernel.const_apply] using hh.symm

end TailGrowth

end

end OAI
