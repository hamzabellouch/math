import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormIteratedFDerivCompLinear
import OAI.Geometry.SmoothYau.Smoothness.ProbabilityBadJet

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem finite_section_score_expectation
    {Ω X J : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (E : J → Set (Ω×X)) (hE : ∀ j, MeasurableSet (E j)) (p : ℝ)
    (hprob : ∀ᵐ x ∂ν, p ≤ ∑ j, (μ {ω | (ω,x) ∈ E j}).toReal) :
    Integrable (fun ω => ∑ j, (ν {x | (ω,x) ∈ E j}).toReal) μ ∧
    (∀ ω, 0 ≤ ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∧
      ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ≤ (Fintype.card J : ℝ)*(ν univ).toReal) ∧
    p*(ν univ).toReal ≤ ∫ ω, ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∂μ := by
  classical
  have hm (j : J) : Measurable (fun ω => (ν {x | (ω,x) ∈ E j}).toReal) :=
    (measurable_measure_prodMk_left (ν := ν) (hE j)).ennreal_toReal
  have hn (j : J) : Measurable (fun x => (μ {ω | (ω,x) ∈ E j}).toReal) :=
    (measurable_measure_prodMk_right (μ := μ) (hE j)).ennreal_toReal
  have hb (j : J) (ω : Ω) : (ν {x | (ω,x) ∈ E j}).toReal ≤ (ν univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hi (j : J) : Integrable (fun ω => (ν {x | (ω,x) ∈ E j}).toReal) μ := by
    apply (integrable_const ((ν univ).toReal)).mono' (hm j).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb j ω
  have hi' (j : J) : Integrable (fun x => (μ {ω | (ω,x) ∈ E j}).toReal) ν := by
    apply (integrable_const (1 : ℝ)).mono' (hn j).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))).trans_eq (by simp)
  have heq (j : J) : (∫ ω, (ν {x | (ω,x) ∈ E j}).toReal ∂μ) =
      ∫ x, (μ {ω | (ω,x) ∈ E j}).toReal ∂ν := by
    calc
      _ = (∫⁻ ω, ν {x | (ω,x) ∈ E j} ∂μ).toReal :=
        integral_toReal (measurable_measure_prodMk_left (ν := ν) (hE j)).aemeasurable
          (ae_of_all _ (fun _ => measure_lt_top _ _))
      _ = (∫⁻ x, μ {ω | (ω,x) ∈ E j} ∂ν).toReal :=
        congrArg ENNReal.toReal ((Measure.prod_apply (μ := μ) (ν := ν) (hE j)).symm.trans
          (Measure.prod_apply_symm (μ := μ) (ν := ν) (hE j)))
      _ = _ := (integral_toReal
        (measurable_measure_prodMk_right (μ := μ) (hE j)).aemeasurable
          (ae_of_all _ (fun _ => measure_lt_top _ _))).symm

  refine ⟨integrable_finsetSum _ (fun j _ => hi j),?_,?_⟩
  · intro ω
    refine ⟨Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg),?_⟩
    calc
      _ ≤ ∑ _j : J, (ν univ).toReal := Finset.sum_le_sum (fun j _ => hb j ω)
      _ = _ := by simp
  · calc
      _ = ∫ _x, p ∂ν := by simp [mul_comm,Measure.real]
      _ ≤ ∫ x, ∑ j, (μ {ω | (ω,x) ∈ E j}).toReal ∂ν :=
        integral_mono_ae (integrable_const p) (integrable_finsetSum _ (fun j _ => hi' j)) hprob
      _ = ∫ ω, ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∂μ := by
        rw [integral_finsetSum _ (fun j _ => hi' j),integral_finsetSum _ (fun j _ => hi j)]
        exact Finset.sum_congr rfl (fun j _ => (heq j).symm)
end


section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
lemma continuous_finiteWaveSuperposition_joint {I X : Type*} [Fintype I]
    [TopologicalSpace X] (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j)) :
    Continuous (fun q : (I → Fin 3 → ℂ) × X => finiteWaveSuperposition w U q.1 q.2) := by
  classical
  unfold finiteWaveSuperposition
  apply (hw.comp continuous_snd).add
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  have hc : Continuous (fun q : (I → Fin 3 → ℂ) × X => q.1 i j) := by fun_prop
  exact Complex.continuous_re.comp (hc.mul ((hU i j).comp continuous_snd))

theorem actual_wave_sign_expectation {I J X : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j))
    (S : J → X → X) (hS : ∀ j, Continuous (S j))
    (ν : Measure X) [IsFiniteMeasure ν] (p : ℝ)
    (hprob : ∀ᵐ x ∂ν, ∃ j, ENNReal.ofReal p ≤
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition w U γ x * finiteWaveSuperposition w U γ (S j x) < 0}) :
    let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
    let F := fun γ => ∑ j, (ν {x | finiteWaveSuperposition w U γ x *
      finiteWaveSuperposition w U γ (S j x) < 0}).toReal
    Integrable F μ ∧ (∀ γ, 0 ≤ F γ ∧ F γ ≤ (Fintype.card J : ℝ)*(ν univ).toReal) ∧
      p*(ν univ).toReal ≤ ∫ γ, F γ ∂μ := by
  classical
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let E : J → Set ((I → Fin 3 → ℂ)×X) := fun j => {q |
    finiteWaveSuperposition w U q.1 q.2 * finiteWaveSuperposition w U q.1 (S j q.2) < 0}
  have hc := continuous_finiteWaveSuperposition_joint w U hw hU
  have hm (j : J) : MeasurableSet (E j) := by
    exact isOpen_lt (hc.mul (hc.comp (continuous_fst.prodMk ((hS j).comp continuous_snd))))
      continuous_const |>.measurableSet
  apply finite_section_score_expectation μ ν E hm p
  filter_upwards [hprob] with x hx
  obtain ⟨j,hj⟩ := hx
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mp hj |>.trans
  apply Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)

theorem exists_large_score_avoiding {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Integrable F μ)
    (B : Set Ω) (C a c : ℝ) (hC : ∀ ω, F ω ≤ C) (hc : 0 ≤ c)
    (ha : a ≤ ∫ ω, F ω ∂μ) (hbad : c+C*(μ B).toReal < a) :
    ∃ ω, ω ∉ B ∧ c < F ω := by
  obtain ⟨ω,hω,hscore⟩ := exists_good_of_expectation μ F hF (toMeasurable μ B)ᶜ
    (measurableSet_toMeasurable μ B).compl C a c hC hc ha (by
      simpa only [compl_compl,measure_toMeasurable] using hbad)
  exact ⟨ω,fun h => hω (subset_toMeasurable μ B h),hscore⟩
end


open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

theorem finite_regions_wave_sign_expectation {I P X : Type*} [Fintype I] [Fintype P]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j))
    (S : P → Fin 3 → X → X) (hS : ∀ a j, Continuous (S a j))
    (ν : P → Measure X) [∀ a, IsFiniteMeasure (ν a)]
    (q : P → ℝ) (hq : ∀ a, 0 ≤ q a) (p : ℝ)
    (hprob : ∀ a, ∀ᵐ x ∂ν a, ∃ j, ENNReal.ofReal p ≤
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition w U γ x * finiteWaveSuperposition w U γ (S a j x) < 0}) :
    let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
    let V := ∑ a, q a*(ν a univ).toReal
    let F := fun γ => ∑ a, q a*∑ j, (ν a {x | finiteWaveSuperposition w U γ x *
      finiteWaveSuperposition w U γ (S a j x) < 0}).toReal
    Integrable F μ ∧ (∀ γ, 0 ≤ F γ ∧ F γ ≤ 3*V) ∧
      p*V ≤ ∫ γ, F γ ∂μ := by
  classical
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let f := fun a γ => ∑ j, (ν a {x | finiteWaveSuperposition w U γ x *
    finiteWaveSuperposition w U γ (S a j x) < 0}).toReal
  have hh (a : P) := actual_wave_sign_expectation w U hw hU (S a) (hS a) (ν a) p (hprob a)
  change (∀ a : P, Integrable (f a) μ ∧ (∀ γ, 0 ≤ f a γ ∧
    f a γ ≤ (Fintype.card (Fin 3) : ℝ)*(ν a univ).toReal) ∧
    p*(ν a univ).toReal ≤ ∫ γ, f a γ ∂μ) at hh
  dsimp only
  refine ⟨integrable_finsetSum _ (fun a _ => (hh a).1.const_mul (q a)),?_,?_⟩
  · intro γ
    refine ⟨Finset.sum_nonneg (fun a _ => mul_nonneg (hq a) ((hh a).2.1 γ).1),?_⟩
    calc
      _ ≤ ∑ a, q a*(3*(ν a univ).toReal) := by
        apply Finset.sum_le_sum; intro a ha
        apply mul_le_mul_of_nonneg_left _ (hq a)
        simpa only [Fintype.card_fin,Nat.cast_ofNat] using ((hh a).2.1 γ).2
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring
  · rw [integral_finsetSum _ (fun a _ => (hh a).1.const_mul (q a)),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [integral_const_mul]
    calc
      _ = q a*(p*(ν a univ).toReal) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hh a).2.2 (hq a)

end YauCounterexamples
end

end OAI
