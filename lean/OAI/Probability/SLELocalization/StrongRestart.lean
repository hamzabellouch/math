import Mathlib
import OAI.Probability.SLELocalization.BrownianSupport
import OAI.Probability.SLELocalization.CommonClocks
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Brownian Predictable estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable

lemma aemeasurable_select_nat {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {Y : Ω → ℕ} (hY : AEMeasurable Y P) (F : ℕ → Ω → E)
    (hF : ∀ k, AEMeasurable (F k) P) : AEMeasurable (fun sample => F (Y sample) sample) P := by
  have hm : Measurable (fun x : ℕ × (ℕ → E) => x.2 x.1) :=
    measurable_from_prod_countable_right (fun k => measurable_pi_apply k)
  exact hm.comp_aemeasurable (hY.prodMk (AEMeasurable.of_eval hF))

lemma measure_nat_partition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℕ} (hY : AEMeasurable Y P) (S : Set Ω) (hS : NullMeasurableSet S P) :
    P S = ∑' k : ℕ, P (S ∩ {sample | Y sample = k}) := by
  have hpieces (k : ℕ) : NullMeasurableSet (S ∩ {sample | Y sample = k}) P :=
    hS.inter (hY.nullMeasurableSet_preimage (measurableSet_singleton k))
  have hd : Pairwise (fun i j : ℕ => Disjoint (S ∩ {sample | Y sample = i})
      (S ∩ {sample | Y sample = j})) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro sample hi hj
    exact hij (hi.2.symm.trans hj.2)
  have he : (⋃ k : ℕ, S ∩ {sample | Y sample = k}) = S := by
    ext sample
    simp
  calc
    P S = P (⋃ k : ℕ, S ∩ {sample | Y sample = k}) := congrArg P he.symm
    _ = _ := measure_iUnion₀ (fun i j hij => (hd hij).aedisjoint) hpieces

lemma countable_restart_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (Y : Ω → ℕ) (hY : AEMeasurable Y P)
    (s : ℕ → ℝ≥0) (A : Set Ω) (hA : NullMeasurableSet A P) (hA0 : P A ≠ 0)
    (hpieces : ∀ k, MeasurableSet[pastSigma B (s k)] (A ∩ {sample | Y sample = k}))
    (I : Finset ℝ≥0) :
    HasLaw (fun sample => I.restrict (fun t => B (s (Y sample)+t) sample-B (s (Y sample)) sample))
      (BrownianReal.projectiveFamily I) ((P A)⁻¹ • P.restrict A) := by
  let F (k : ℕ) (sample : Ω) := I.restrict (fun t => B (s k+t) sample-B (s k) sample)
  have hF (k : ℕ) : HasLaw (F k) (BrownianReal.projectiveFamily I) P :=
    (hB.shift (s k)).toIsPreBrownianReal.hasLaw I
  let X := fun sample => F (Y sample) sample
  have hX : AEMeasurable X P := aemeasurable_select_nat hY F (fun k => (hF k).aemeasurable)
  refine ⟨hX.restrict.smul_measure _,?_⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply_of_aemeasurable (hX.restrict.smul_measure _) hE,
    Measure.smul_apply,smul_eq_mul,Measure.restrict_apply₀ (hX.restrict.nullMeasurableSet_preimage hE),inter_comm]
  have hind (k : ℕ) : P ((A ∩ {sample | Y sample = k}) ∩ (F k ⁻¹' E)) =
      P (A ∩ {sample | Y sample = k}) * (BrownianReal.projectiveFamily I) E := by
    have hi := (hB.toIsPreBrownianReal.indepFun_shift (s k)).symm.comp
      measurable_id (show Measurable (fun f : ℝ≥0 → ℝ => I.restrict f) from
        Measurable.of_eval (fun t => measurable_pi_apply (t : ℝ≥0)))
    have hh := hi.meas_inter (hpieces k) (hE.preimage (comap_measurable (F k)))
    have hll : P (F k ⁻¹' E) = (BrownianReal.projectiveFamily I) E := (hF k).measure_eq hE
    rw [hll] at hh
    exact hh
  have he (k : ℕ) : (A ∩ X ⁻¹' E) ∩ {sample | Y sample = k} =
      (A ∩ {sample | Y sample = k}) ∩ F k ⁻¹' E := by
    ext sample
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,X]
    constructor
    · rintro ⟨⟨ha,hf⟩,hy⟩
      exact ⟨⟨ha,hy⟩,hy ▸ hf⟩
    · rintro ⟨⟨ha,hy⟩,hf⟩
      exact ⟨⟨ha,hy ▸ hf⟩,hy⟩
  rw [measure_nat_partition hY (A ∩ X ⁻¹' E) (hA.inter (hX.nullMeasurableSet_preimage hE))]
  simp_rw [he,hind]
  rw [ENNReal.tsum_mul_right,← measure_nat_partition hY A hA,← mul_assoc,
    ENNReal.inv_mul_cancel hA0 (measure_ne_top P A),one_mul]

lemma hasLaw_of_ae_limit {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} [IsFiniteMeasure P]
    {μ : Measure E} [IsFiniteMeasure μ] {X : ℕ → Ω → E} {Y : Ω → E}
    (hX : ∀ n, HasLaw (X n) μ P)
    (hlim : ∀ᵐ sample ∂P, Tendsto (fun n => X n sample) atTop (𝓝 (Y sample))) : HasLaw Y μ P := by
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (hX n).aemeasurable) hlim
  refine ⟨hY,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hY φ.continuous.measurable.aestronglyMeasurable]
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n sample => φ (X n sample)) (f := fun sample => φ (Y sample)) (fun _ : Ω => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp_aemeasurable (hX n).aemeasurable).aestronglyMeasurable)
    (integrable_const ‖φ‖) (fun n => Filter.Eventually.of_forall (fun sample => φ.norm_coe_le_norm _))
    (hlim.mono (fun sample hh => φ.continuous.continuousAt.tendsto.comp hh))
  have he (n : ℕ) : (∫ sample, φ (X n sample) ∂P) = ∫ x, φ x ∂μ :=
    (hX n).integral_comp φ.continuous.measurable.aestronglyMeasurable
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem brownianStrongRestart {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (τ : Ω → ℝ≥0) (hτ : AEMeasurable τ P)
    (A : Set Ω) (hA : NullMeasurableSet A P) (hA0 : P A ≠ 0)
    (hstop : ∀ t : ℝ≥0, MeasurableSet[pastSigma B t] (A ∩ {sample | τ sample ≤ t})) :
    IsBrownianReal (fun t sample => B (τ sample+t) sample-B (τ sample) sample)
      ((P A)⁻¹ • P.restrict A) := by
  let Q : Measure Ω := (P A)⁻¹ • P.restrict A
  have hQP : Q ≪ P := Measure.smul_absolutelyContinuous.trans
    Measure.restrict_le_self.absolutelyContinuous
  have : IsProbabilityMeasure Q := ⟨by
    simp only [Q,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hA0 (measure_ne_top P A)⟩
  have hc : ∀ᵐ sample ∂Q, Continuous (fun t => B t sample) := hQP.ae_le hB.cont
  refine ⟨⟨fun I => ?_⟩,?_⟩
  · apply hasLaw_of_ae_limit (X := fun n sample =>
      I.restrict (fun t => B (restartTime τ n sample+t) sample-B (restartTime τ n sample) sample))
    · intro n
      exact countable_restart_law hB (restartIndex τ n) (restartIndex_aemeasurable hτ n)
        (restartGrid n) A hA hA0 (restartIndex_past B τ A hstop n) I
    · filter_upwards [hc] with sample hh
      apply tendsto_pi_nhds.2
      intro t
      exact ((hh.continuousAt.tendsto.comp ((restartTime_tendsto τ sample).add tendsto_const_nhds)).sub
        (hh.continuousAt.tendsto.comp (restartTime_tendsto τ sample)))
  · filter_upwards [hc] with sample hh
    exact (hh.comp (continuous_const.add continuous_id)).sub continuous_const

end SLEExactGauge.BrownianPredictable

end

end

end OAI
