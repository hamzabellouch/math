import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! The Brownian germ zero-one argument needed for positive canonical
mass before every positive time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

lemma brownian_germ_fdd_law
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (E : Set Ω)
    (hE : ∀ n, MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε n)] E)
    (I : Finset ℝ≥0) :
    (P.restrict E).map (fun ω => I.restrict (fun t => B t ω)) =
      P E • BrownianReal.projectiveFamily I := by
  let : IsFiniteMeasure (P E • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P E)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  have hXm : Measurable (fun ω => I.restrict (fun t => B t ω)) :=
    (Finset.measurable_restrict I).comp (Measurable.of_eval hm)
  rw [integral_map hXm.aemeasurable φ.continuous.aestronglyMeasurable, integral_smul_measure]
  have ht (ω : Ω) : Tendsto (fun n => shiftedFDD B I (ε n) ω) atTop
      (𝓝 (I.restrict (fun t => B t ω))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    change Tendsto (fun n => B (ε n+(i:ℝ≥0)) ω-B (ε n) ω) atTop (𝓝 (B (i:ℝ≥0) ω))
    have hh := ((hc ω).continuousAt.tendsto.comp (hε.add_const (i:ℝ≥0))).sub
      ((hc ω).continuousAt.tendsto.comp hε)
    simpa only [Function.comp_def,zero_add,h0 ω,sub_zero] using hh
  have hi := tendsto_integral_of_dominated_convergence (μ:=P.restrict E)
    (F:=fun n ω => φ (shiftedFDD B I (ε n) ω))
    (f:=fun ω => φ (I.restrict (fun t => B t ω))) (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp (shiftedFDD_measurable hm I (ε n))).aestronglyMeasurable)
    (integrable_const _) (fun _ => Eventually.of_forall (fun _ => φ.norm_coe_le_norm _))
    (Eventually.of_forall (fun ω => φ.continuous.continuousAt.tendsto.comp (ht ω)))
  simp only [shiftedFDD_setIntegral hB hm I _ φ (hE _)] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

lemma brownian_germ_path_law
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (E : Set Ω)
    (hE : ∀ n, MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε n)] E) :
    (P.restrict E).map (fun ω t => B t ω) = P E • P.map (fun ω t => B t ω) := by
  let (I : Finset ℝ≥0) : IsFiniteMeasure (P E • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P E)
  have hL : IsProjectiveLimit ((P.restrict E).map (fun ω t => B t ω))
      (fun I => P E • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm)]
    exact brownian_germ_fdd_law hB hm hc h0 ε hε E hE I
  have hR : IsProjectiveLimit (P E • P.map (fun ω t => B t ω))
      (fun I => P E • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_smul _ (Finset.measurable_restrict I).aemeasurable,
      Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm)]
    exact congrArg (fun μ => P E • μ) (hB.hasLaw I).map_eq
  exact hL.unique hR

/-- An event observable along times decreasing to zero has probability
zero or one. Only the continuous based Brownian path is needed. -/
theorem brownian_germ_zero_one
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (E : Set Ω)
    (hE : ∀ n, MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε n)] E) :
    P E=0 ∨ P E=1 := by
  have hevent := hE 0
  rw [Filtration.natural_eq_comap B _ (ε 0)] at hevent
  obtain ⟨D,hD,heD⟩ := hevent
  let A : Set (ℝ≥0 → ℝ) := (fun b => fun s : Iic (ε 0) => b s) ⁻¹' D
  have hr : Measurable (fun b : ℝ≥0 → ℝ => fun s : Iic (ε 0) => b (s:ℝ≥0)) :=
    Measurable.of_eval (fun s => measurable_pi_apply (s:ℝ≥0))
  have hA : MeasurableSet A := hr hD
  have hpre : (fun ω t => B t ω) ⁻¹' A=E := heD
  have hEm : MeasurableSet E := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le (ε 0) E (hE 0)
  have he := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ A)
    (brownian_germ_path_law hB hm hc h0 ε hε E hE)
  rw [Measure.map_apply (Measurable.of_eval hm) hA,Measure.smul_apply,
    Measure.map_apply (Measurable.of_eval hm) hA,hpre,Measure.restrict_apply hEm,inter_self] at he
  by_cases hz : P E=0
  · exact Or.inl hz
  · right
    apply (ENNReal.mul_left_inj hz (measure_ne_top P E)).mp
    simpa only [smul_eq_mul,one_mul] using he.symm

end SLEExactGauge

end

end OAI
