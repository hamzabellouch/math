import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

namespace OAI

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace InvariantProjection.IndependentAngles

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_add_ne_of_indep [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    [NullSingletonClass (μ.map Y)] (c : ℝ) :
    ∀ᵐ ω ∂μ, X ω + Y ω ≠ c := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≠ c} := by
    exact (measurable_fst.add measurable_snd) (measurableSet_singleton c).compl
  have hp : ∀ᵐ z ∂(μ.map X).prod (μ.map Y), z.1 + z.2 ≠ c := by
    apply (ae_prod_iff_ae_ae hset).2
    exact Filter.Eventually.of_forall fun x =>
      ((μ.map Y).ae_ne (c - x)).mono fun y hy h => hy (by linarith)
  rw [← hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable] at hp
  exact ae_of_ae_map (hX.prodMk hY).aemeasurable hp

theorem nullSingletonClass_map_mul {X : Ω → ℝ} (hX : Measurable X)
    [NullSingletonClass (μ.map X)] {c : ℝ} (hc : c ≠ 0) :
    NullSingletonClass (μ.map (fun ω => c * X ω)) := by
  constructor
  intro y
  rw [Measure.map_apply (show Measurable (fun ω => c * X ω) from
    measurable_const.mul hX) (measurableSet_singleton y)]
  have hsub : (fun ω => c * X ω) ⁻¹' {y} ⊆ X ⁻¹' {y / c} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    apply (eq_div_iff hc).2
    simpa [mul_comm] using hω
  apply measure_mono_null hsub
  rw [← Measure.map_apply hX (measurableSet_singleton (y / c))]
  exact measure_singleton _

theorem ae_finset_sum_ne [IsProbabilityMeasure μ] [DecidableEq ι]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (s : Finset ι) (c : ι → ℝ) {i : ι} (hi : i ∈ s) (hci : c i ≠ 0)
    (r : ℝ) : ∀ᵐ ω ∂μ, (∑ j ∈ s, c j * X j ω) ≠ r := by
  let Y : ι → Ω → ℝ := fun j ω => c j * X j ω
  have hY : ∀ j, Measurable (Y j) := fun j => measurable_const.mul (hX j)
  have hindY : iIndepFun Y μ := hind.comp (fun j x => c j * x)
    (fun _ => measurable_const.mul measurable_id)
  have hsumInd : IndepFun (∑ j ∈ s.erase i, Y j) (Y i) μ :=
    hindY.indepFun_finsetSum_of_notMem hY (Finset.notMem_erase i s)
  let : NullSingletonClass (μ.map (X i)) := hno i
  let : NullSingletonClass (μ.map (Y i)) :=
    nullSingletonClass_map_mul (hX i) hci
  have hsum : Measurable (∑ j ∈ s.erase i, Y j) := by
    change Measurable (fun ω => (∑ j ∈ s.erase i, Y j) ω)
    simp only [Finset.sum_apply]
    exact Finset.measurable_sum (s.erase i) (fun j _ => hY j)
  filter_upwards [ae_add_ne_of_indep hsum (hY i) hsumInd r] with ω hω
  convert hω using 1
  simp only [Finset.sum_apply, Y]
  exact (Finset.sum_erase_add _ _ hi).symm

theorem ae_finsupp_sum_ne [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (c : ι →₀ ℚ) (hc : c ≠ 0) (r : ℝ) :
    ∀ᵐ ω ∂μ, c.sum (fun j q => (q : ℝ) * X j ω) ≠ r := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hci : (c i : ℝ) ≠ 0 := by
    exact_mod_cast Finsupp.mem_support_iff.mp hi
  exact ae_finset_sum_ne hX hind hno c.support (fun j => (c j : ℝ)) hi hci r

theorem ae_no_rational_affine_relation [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, ∀ (c : ι →₀ ℚ) (q : ℚ),
      (q : ℝ) + c.sum (fun j r => (r : ℝ) * X j ω) = 0 → c = 0 ∧ q = 0 := by
  apply ae_all_iff.mpr
  intro c
  apply ae_all_iff.mpr
  intro q
  by_cases hc : c = 0
  · subst c
    exact Filter.Eventually.of_forall fun ω h => ⟨rfl, by simpa using h⟩
  · filter_upwards [ae_finsupp_sum_ne hX hind hno c hc (-(q : ℝ))] with ω hω
    intro heq
    exact False.elim (hω (by linarith))

theorem ae_linearIndependent_with_one [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, LinearIndependent ℚ (fun o : Option ι => o.elim 1 (fun i => X i ω)) := by
  filter_upwards [ae_no_rational_affine_relation hX hind hno] with ω hω
  rw [linearIndependent_iff]
  intro l hl
  rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul] at hl
  have hrel : (l none : ℝ) + l.some.sum (fun j r => (r : ℝ) * X j ω) = 0 := by
    simpa only [Option.elim_none, Option.elim_some, Rat.smul_def, mul_one] using hl
  obtain ⟨hsome, hnone⟩ := hω l.some (l none) hrel
  ext o
  cases o with
  | none => exact hnone
  | some i =>
      change l.some i = 0
      rw [hsome]
      rfl

theorem infinitePi_ae_linearIndependent_with_one [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] :
    ∀ᵐ θ ∂Measure.infinitePi ν,
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hm : ∀ i : ι, Measurable (fun θ : ι → ℝ => θ i) :=
    fun i => measurable_pi_apply i
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hn : ∀ i : ι, NullSingletonClass
      ((Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i)) := by
    intro i
    rw [Measure.infinitePi_map_eval]
    infer_instance
  exact ae_linearIndependent_with_one hm hi hn

theorem exists_linearIndependent_with_one_and [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] {P : (ι → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi ν, P θ) :
    ∃ θ : ι → ℝ, LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) ∧ P θ :=
  ((infinitePi_ae_linearIndependent_with_one ν).and hP).exists

theorem intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem intervalLaw_nullSingletonClass (a b : ℝ) :
    NullSingletonClass (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  constructor
  intro x
  exact ProbabilityTheory.cond_absolutelyContinuous (measure_singleton x)

theorem intervalProduct_ae_bounds_linearIndependent [Countable ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))),
      (∀ i, θ i ∈ Set.Icc (a i) (b i)) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  let ν : ι → Measure ℝ := fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))
  let (i : ι) : IsProbabilityMeasure (ν i) := intervalLaw_isProbabilityMeasure (hab i)
  let (i : ι) : NullSingletonClass (ν i) := intervalLaw_nullSingletonClass (a i) (b i)
  have hb : ∀ᵐ θ ∂Measure.infinitePi ν, ∀ i, θ i ∈ Set.Icc (a i) (b i) := by
    apply ae_all_iff.mpr
    intro i
    have hi : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ => θ i),
        x ∈ Set.Icc (a i) (b i) := by
      rw [Measure.infinitePi_map_eval]
      exact ae_cond_mem measurableSet_Icc
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  exact hb.and (infinitePi_ae_linearIndependent_with_one ν)

theorem exists_interval_bounds_linearIndependent [Countable ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∃ θ : ι → ℝ, (∀ i, θ i ∈ Set.Icc (a i) (b i)) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  let (i : ι) : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (a i) (b i))) :=
    intervalLaw_isProbabilityMeasure (hab i)
  exact (intervalProduct_ae_bounds_linearIndependent a b hab).exists

theorem prescribedIntervals_ae_summable_independent [Countable ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (hsum : Summable (fun i => 1 / N i)) :
    ∀ᵐ θ ∂Measure.infinitePi
        (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))),
      (∀ i, θ i ∈ Set.Icc (1 / N i) (2 / N i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / N i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hinterval : ∀ i, (1 : ℝ) / N i < 2 / N i := fun i =>
    div_lt_div_of_pos_right (by norm_num) (hN i)
  filter_upwards [intervalProduct_ae_bounds_linearIndependent
    (fun i => 1 / N i) (fun i => 2 / N i) hinterval] with θ hθ
  have hnonneg : ∀ i, 0 ≤ θ i := fun i =>
    (le_of_lt (one_div_pos.mpr (hN i))).trans (hθ.1 i).1
  have hupper : ∀ i, θ i ≤ 2 * (1 / N i) := by
    intro i
    simpa only [mul_one_div] using (hθ.1 i).2
  have hsumθ : Summable θ :=
    Summable.of_nonneg_of_le hnonneg hupper (hsum.mul_left 2)
  refine ⟨hθ.1, hsumθ, ?_, hθ.2⟩
  calc
    (∑' i, θ i) ≤ ∑' i, 2 * (1 / N i) :=
      hsumθ.tsum_le_tsum hupper (hsum.mul_left 2)
    _ = 2 * (∑' i, 1 / N i) := tsum_mul_left

theorem exists_prescribed_summable_independent_and [Countable ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (hsum : Summable (fun i => 1 / N i))
    {P : (ι → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))), P θ) :
    ∃ θ : ι → ℝ, (∀ i, θ i ∈ Set.Icc (1 / N i) (2 / N i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / N i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) ∧ P θ := by
  let (i : ι) : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))) :=
    intervalLaw_isProbabilityMeasure (div_lt_div_of_pos_right (by norm_num) (hN i))
  obtain ⟨θ, hθ, hp⟩ :=
    ((prescribedIntervals_ae_summable_independent N hN hsum).and hP).exists
  exact ⟨θ, hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2, hp⟩

end InvariantProjection.IndependentAngles

end OAI
