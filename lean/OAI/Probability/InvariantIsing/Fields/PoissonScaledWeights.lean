import OAI.Probability.IsingPerceptron.RetainedDisplacement
import OAI.Probability.IsingPerceptron.VariationalDefs

namespace OAI

/-! Distinct active Poisson weights after deterministic positive rescaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal NNReal
namespace InvariantIsing

lemma independent_scaled_ne (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν] (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, c * p.1 ≠ d * p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)).compl).mpr
  refine ae_of_all _ fun x => ?_
  have h : ∀ᵐ y ∂ν, y ≠ c * x / d := by
    rw [ae_iff]
    convert (measure_singleton (c * x / d) : ν {c * x / d} = 0) using 1
    congr 1
    ext y
    simp
  filter_upwards [h] with y hy he
  apply hy
  exact (eq_div_iff hd).mpr (by simpa only [Pi.mul_apply, mul_comm] using he.symm)

lemma finiteMeasure_normalize_noAtoms (μ : FiniteMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : μ ≠ 0) :
    NullSingletonClass (μ.normalize : Measure ℝ) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero hμ]
  constructor
  intro x
  simp only [Measure.smul_apply, measure_singleton, smul_zero]

lemma finitePoissonCloud_point_law (μ : FiniteMeasure ℝ) (i : ℕ) :
    MeasurePreserving (fun p : ℕ × (ℕ → ℝ) => p.2 i)
      (finitePoissonCloud μ.mass (μ.normalize : Measure ℝ)) (μ.normalize : Measure ℝ) := by
  exact (measurePreserving_eval_infinitePi _ i).comp
    (measurePreserving_snd (μ := poissonMeasure μ.mass)
      (ν := Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ)))

lemma finitePoissonCloud_zero_inactive (i : ℕ) :
    ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (0 : FiniteMeasure ℝ).mass
      ((0 : FiniteMeasure ℝ).normalize : Measure ℝ), ¬ i < p.1 := by
  have h : ∀ᵐ n : ℕ ∂poissonMeasure (0 : FiniteMeasure ℝ).mass, n = 0 := by
    simp [poissonMeasure_zero_eq_dirac]
  have hm := (measurePreserving_fst (μ := poissonMeasure (0 : FiniteMeasure ℝ).mass)
    (ν := Measure.infinitePi fun _ : ℕ => ((0 : FiniteMeasure ℝ).normalize : Measure ℝ)))
  filter_upwards [hm.quasiMeasurePreserving.tendsto_ae.eventually h] with p hp
  simp [hp]

lemma finitePoissonCloud_scaled_distinct (μ : FiniteMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : μ ≠ 0)
    (i j : ℕ) (hij : i ≠ j) (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud μ.mass (μ.normalize : Measure ℝ),
      c * p.2 i ≠ d * p.2 j := by
  let : NullSingletonClass (μ.normalize : Measure ℝ) := finiteMeasure_normalize_noAtoms μ hμ
  have hpair : MeasurePreserving (fun g : ℕ → ℝ => (g i,g j))
      (Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ))
      ((μ.normalize : Measure ℝ).prod (μ.normalize : Measure ℝ)) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hij⟩
  exact ((hpair.comp (measurePreserving_snd (μ := poissonMeasure μ.mass)
    (ν := Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ)))).quasiMeasurePreserving.tendsto_ae.eventually
      (independent_scaled_ne _ _ c d hd))

end InvariantIsing

end

end OAI
