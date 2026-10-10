import OAI.Geometry.TranslativeCovering.PoissonSample

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
variable {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]

lemma measurable_injective (n : ℕ) :
    MeasurableSet {f : Fin n → Ω | Function.Injective f} := by
  simp only [Function.Injective, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl

lemma ae_injective (n : ℕ) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] :
    ∀ᵐ f ∂Measure.pi (fun _ : Fin n => σ), Function.Injective f := by
  have hall (i j : Fin n) : ∀ᵐ f ∂Measure.pi (fun _ : Fin n => σ), i ≠ j → f i ≠ f j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hind := (iIndepFun_pi (μ := fun _ : Fin n => σ) (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable)).indepFun hij
      have hmap := hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => σ) i).map_eq,
        (measurePreserving_eval (fun _ : Fin n => σ) j).map_eq] at hmap
      have hp : ∀ᵐ p : Ω × Ω ∂σ.prod σ, p.1 ≠ p.2 :=
        (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
          (Filter.Eventually.of_forall (fun x => (σ.ae_ne x).mono (fun y hy => hy.symm)))
      rw [← hmap] at hp
      exact (ae_of_ae_map ((measurable_pi_apply i).prodMk
        (measurable_pi_apply j)).aemeasurable hp).mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hall i))] with f hf
  intro i j heq
  by_contra hij
  exact hf i j hij heq

noncomputable def simplify (x : RawConfig Ω) : PoissonConfig.Config Ω :=
  if h : Function.Injective x.2 then ⟨x.1, ⟨x.2,h⟩⟩
  else ⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩

lemma measurable_simplify : Measurable (simplify (Ω := Ω)) := by
  apply PoissonConfig.measurable_sigma
  intro n
  change Measurable (fun f : Fin n → Ω => if h : Function.Injective f then
    (⟨n, ⟨f,h⟩⟩ : PoissonConfig.Config Ω) else ⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩)
  have hm := (measurable_sigmaMk (β := fun k => {f : Fin k → Ω // Function.Injective f}) n).dite
      (g := fun _ => (⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩ : PoissonConfig.Config Ω))
      measurable_const (measurable_injective n)
  convert! hm using 1
  funext f
  split_ifs <;> first | rfl | contradiction

lemma sample_ae_simple (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] : ∀ᵐ x ∂sample r σ, Function.Injective x.2 := by
  rw [sample, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure (c := poissonMeasure r {n})
  have hm : MeasurableSet {x : RawConfig Ω | Function.Injective x.2} :=
    measurableSet_sigma (fun k => measurable_injective k)
  exact (ae_map_iff (measurable_sigmaMk n).aemeasurable hm).mpr (ae_injective n σ)

noncomputable def simpleSample (r : ℝ≥0) (σ : Measure Ω) :
    Measure (PoissonConfig.Config Ω) := (sample r σ).map simplify

instance simpleSample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (simpleSample r σ) :=
  inferInstanceAs (IsProbabilityMeasure ((sample r σ).map simplify))

lemma simpleSample_void (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] :
    PoissonConfig.HasVoidLaw ((r : ℝ≥0∞) • σ) (simpleSample r σ) := by
  constructor
  intro E hE
  have hm : MeasurableSet {x : PoissonConfig.Config Ω | PoissonConfig.count E x = 0} :=
    (PoissonConfig.measurable_count hE) (measurableSet_singleton 0)
  rw [simpleSample, Measure.map_apply measurable_simplify hm]
  have he : simplify ⁻¹' {x | PoissonConfig.count E x = 0} =ᵐ[sample r σ] avoidance E := by
    filter_upwards [sample_ae_simple r σ] with x hx
    change (PoissonConfig.count E (simplify x) = 0) = (∀ i, x.2 i ∉ E)
    simp only [simplify, dite_eq_left hx, PoissonConfig.count_zero_iff]
  rw [measure_congr he, avoidance_prob r σ hE]
  congr 2
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  ring

end PoissonSample

end OAI
