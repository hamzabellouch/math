import Mathlib
import OAI.Probability.SLE.NearRealContraction

namespace OAI

/-! Brownian Strong Markov for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def shiftedFDD {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (I : Finset ℝ≥0) (s : ℝ≥0) (ω : Ω) : I → ℝ :=
  fun i => B (s + i) ω - B s ω

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))

include hm in
lemma shiftedFDD_measurable (I : Finset ℝ≥0) (s : ℝ≥0) :
    Measurable (shiftedFDD B I s) :=
  Measurable.of_eval (fun i => (hm (s + i)).sub (hm s))

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_indep (I : Finset ℝ≥0) (s : ℝ≥0) :
    Indep (Filtration.natural B (fun t => (hm t).stronglyMeasurable) s)
      (MeasurableSpace.comap (shiftedFDD B I s) inferInstance) P := by
  have hi := ((hB.indepFun_shift s).comp
    (Measurable.of_eval (fun i : I => measurable_pi_apply (i : ℝ≥0))) measurable_id).symm
  rw [Filtration.natural_eq_comap B _ s]
  exact (IndepFun_iff_Indep _ _ _).mp hi

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_setIntegral (I : Finset ℝ≥0) (s : ℝ≥0)
    (φ : BoundedContinuousFunction (I → ℝ) ℝ) {A : Set Ω}
    (hA : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] A) :
    (∫ ω in A, φ (shiftedFDD B I s ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  rw [(shiftedFDD_indep hB hm I s).setIntegral_eq_mul
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s)
    (shiftedFDD_measurable hm I s).aemeasurable hA φ.continuous.aestronglyMeasurable]
  congr 1
  exact ((hB.shift s).hasLaw I).integral_comp φ.continuous.aestronglyMeasurable

include hm in
lemma shiftedFDD_grid_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ)
    (I : Finset ℝ≥0) (n : ℕ) :
    Measurable (fun ω => shiftedFDD B I (stopGrid n (τ ω)) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_discrete_eval
    (fun k ω => B (stopGridTime n k + i) ω - B (stopGridTime n k) ω)
    (fun k => (hm _).sub (hm _)) (stopGridIndex_measurable hτm n)

include hB hm in
lemma shiftedFDD_grid_setIntegral {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) (n : ℕ) :
    (∫ ω in A, φ (shiftedFDD B I (stopGrid n (τ ω)) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  apply integral_stopping_grid_glue hτ hA n _
    (Integrable.of_bound (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable
      ‖φ‖ (Eventually.of_forall (fun ω => φ.norm_coe_le_norm _)))
  intro k
  have hk := stopping_grid_piece_measurable hτ hA n k
  have hk' := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le _ _ hk
  rw [setIntegral_congr_fun hk' (g := fun ω => φ (shiftedFDD B I (stopGridTime n k) ω))
    (fun ω hω => by
      have he : stopGridIndex n (τ ω) = k := hω.2
      simp only [Function.comp_def, stopGrid, he])]
  exact shiftedFDD_setIntegral hB hm I _ φ hk

omit mΩ in
lemma shiftedFDD_grid_tendsto
    (hc : ∀ ω, Continuous (fun t => B t ω)) (I : Finset ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n => shiftedFDD B I (stopGrid n (τ ω)) ω) atTop
      (𝓝 (shiftedFDD B I (τ ω) ω)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact ((hc ω).continuousAt.tendsto.comp ((stopGrid_tendsto (τ ω)).add_const (i : ℝ≥0))).sub
    ((hc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω)))

include hB hm in
 

theorem brownian_strongMarkov_integral
    (hc : ∀ ω, Continuous (fun t => B t ω)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) :
    (∫ ω in A, φ (shiftedFDD B I (τ ω) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (F := fun n ω => φ (shiftedFDD B I (stopGrid n (τ ω)) ω))
    (f := fun ω => φ (shiftedFDD B I (τ ω) ω)) (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall (fun ω => φ.norm_coe_le_norm _))
    (Eventually.of_forall (fun ω => φ.continuous.continuousAt.tendsto.comp
      (shiftedFDD_grid_tendsto hc I τ ω)))
  simp only [shiftedFDD_grid_setIntegral hB hm hτ hA I φ] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def brownianRestart {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ := B (τ ω + t) ω - B (τ ω) ω

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
  (hc : ∀ ω, Continuous (fun t => B t ω))

include hm hc in
lemma brownianRestart_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    Measurable (fun ω t => brownianRestart B τ t ω) := by
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  apply Measurable.of_eval
  intro t
  exact (hBm.comp ((hτm.add_const t).prodMk measurable_id)).sub
    (hBm.comp (hτm.prodMk measurable_id))

include hB hm hc in
lemma brownian_restart_fdd_restrict {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => shiftedFDD B I (τ ω) ω) =
      P A • BrownianReal.projectiveFamily I := by
  have hXm : Measurable (fun ω => shiftedFDD B I (τ ω) ω) :=
    (Finset.measurable_restrict I).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ))
  let : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hXm.aemeasurable φ.continuous.aestronglyMeasurable,
    integral_smul_measure]
  exact brownian_strongMarkov_integral hB hm hc hτ hA I φ

include hB hm hc in
 

theorem brownian_restart_path_law {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω t => brownianRestart B τ t ω) =
      P A • P.map (fun ω t => B t ω) := by
  have hXm := brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)
  have hBm : Measurable (fun ω t => B t ω) := Measurable.of_eval hm
  let (I : Finset ℝ≥0) : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  have hL : IsProjectiveLimit ((P.restrict A).map (fun ω t => brownianRestart B τ t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hXm]
    exact brownian_restart_fdd_restrict hB hm hc hτ hA I
  have hR : IsProjectiveLimit (P A • P.map (fun ω t => B t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_smul _ (Finset.measurable_restrict I).aemeasurable,
      Measure.map_map (Finset.measurable_restrict I) hBm]
    exact congrArg (fun ν => P A • ν) (hB.hasLaw I).map_eq
  exact hL.unique hR

include hB hm hc in
lemma brownian_restart_path_map {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    P.map (fun ω t => brownianRestart B τ t ω) = P.map (fun ω t => B t ω) := by
  simpa only [Measure.restrict_univ, measure_univ, one_smul] using
    brownian_restart_path_law hB hm hc hτ (A := univ) MeasurableSet.univ

include hB hm hc in
lemma brownian_restart_event_factorizes {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | (fun t => brownianRestart B τ t ω) ∈ S}) =
      P A * P {ω | (fun t => B t ω) ∈ S} := by
  have hXm := brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)
  have he := congrArg (fun ν : Measure (ℝ≥0 → ℝ) => ν S)
    (brownian_restart_path_law hB hm hc hτ hA)
  rw [Measure.map_apply hXm hS, Measure.restrict_apply (hXm hS),
    Measure.smul_apply, Measure.map_apply (Measurable.of_eval hm) hS] at he
  simpa only [Set.preimage, Set.inter_comm, smul_eq_mul] using he

include hB hm hc in
 

theorem brownian_restart_independent {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (fun ω t => brownianRestart B τ t ω) inferInstance) P := by
  rw [Indep_iff]
  intro A C hA hC
  rcases hC with ⟨S, hS, rfl⟩
  have he := congrArg (fun ν : Measure (ℝ≥0 → ℝ) => ν S)
    (brownian_restart_path_map hB hm hc hτ)
  rw [Measure.map_apply (brownianRestart_measurable hm hc
    (stopping_time_measurable_nnreal hτ)) hS,
    Measure.map_apply (Measurable.of_eval hm) hS] at he
  change P (A ∩ {ω | (fun t => brownianRestart B τ t ω) ∈ S}) = _
  rw [brownian_restart_event_factorizes hB hm hc hτ hA hS]
  rw [he]
  rfl

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

section
variable {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
  (U : ℝ≥0 → Ω → ℝ) (hUa : Adapted ℱ U)
  (hUc : ∀ ω, Continuous (fun t => U t ω))
include hUa hUc

lemma measurable_reverse_driver (T : ℝ≥0) :
    @Measurable (ℝ × Ω) ℝ ((borel ℝ).prod (ℱ T)) (borel ℝ)
      (fun p => U (min ((T : ℝ) - p.1).toNNReal T) p.2) := by
  have hsa : StronglyAdapted ℱ U := fun t => (hUa t).stronglyMeasurable
  have hp := (hsa.isStronglyProgressive_of_continuous hUc T).measurable
  let : MeasurableSpace Ω := ℱ T
  have ht : Measurable (fun s : ℝ => (⟨min ((T : ℝ) - s).toNNReal T,
      by change min ((T : ℝ) - s).toNNReal T ≤ T; exact min_le_right _ _⟩ : Iic T)) :=
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).min continuous_const).measurable.subtype_mk
  exact hp.comp ((ht.comp measurable_fst).prodMk measurable_snd)

 

theorem inverse_vertical_measurable
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (h : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω))
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    @Measurable Ω ℂ (ℱ T) (borel ℂ)
      (fun ω => F ω T ((U T ω : ℂ) + (a : ℂ) * I)) := by
  let V (s : ℝ) (ω : Ω) := U (min ((T : ℝ) - s).toNNReal T) ω
  have hVm := measurable_reverse_driver ℱ U hUa hUc T
  have hVc (ω : Ω) : Continuous (fun s : ℝ => V s ω) :=
    (hUc ω).comp ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).min continuous_const)
  let : MeasurableSpace Ω := ℱ T
  have hwm : Measurable (fun ω => (U T ω : ℂ) + (a : ℂ) * I) :=
    (Complex.continuous_ofReal.measurable.comp (hUa T)).add_const _
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_measurable_reverse_flow V hVm hVc
    (fun ω => (U T ω : ℂ) + (a : ℂ) * I) hwm ha
  have he (ω : Ω) : Q (T : ℝ) ω = F ω T ((U T ω : ℂ) + (a : ℂ) * I) := by
    apply (h ω).reverse_flow_identifies T _ ha (by simp) (fun s => Q s ω) (hQ0 ω)
    intro s hs
    have hsT : ((T : ℝ) - s).toNNReal ≤ T :=
      Real.toNNReal_le_iff_le_coe.mpr (by linarith [hs.1])
    simpa only [V, min_eq_left hsT] using
      (hQd ω s hs.1).mono (show Icc (0 : ℝ) T ⊆ Ici 0 from Icc_subset_Ici_self)
  have hefun : (fun ω => Q (T : ℝ) ω) = (fun ω => F ω T ((U T ω : ℂ) + (a : ℂ) * I)) := funext he
  rw [← hefun]
  exact hQm.comp (measurable_prodMk_left (x := (T : ℝ)))

 

theorem capacity_trace_adapted
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (h : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω)) :
    Adapted ℱ (fun t ω => γ ω t) := by
  intro T
  have hn (n : ℕ) : @Measurable Ω ℂ (ℱ T) (borel ℂ)
      (fun ω => F ω T ((U T ω : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)) :=
    inverse_vertical_measurable ℱ U hUa hUc γ G F h T (by positivity)
  let : MeasurableSpace Ω := ℱ T
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => F ω T ((U T ω : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I))
  · exact hn
  · apply tendsto_pi_nhds.mpr
    intro ω
    have hy : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall (fun n => by change (0 : ℝ) < 1 / ((n : ℝ) + 1); positivity)⟩
    exact ((h ω).2.2.2.2.2.2.2.2.2.2.2.2 T).comp hy

end
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
def IsCapacityTwoTrace (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) : Prop :=
  ∃ G F : ℝ≥0 → ℂ → ℂ, IsCapacityTwoWitness U γ G F

 

def IsOrdinaryChordalSLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (P : Measure Ω) : Prop :=
  (∀ t, Measurable (fun ω => γ ω t)) ∧
  ∃ B : ℝ≥0 → Ω → ℝ, ProbabilityTheory.IsBrownianReal B P ∧
    ∀ᵐ ω ∂P, IsCapacityTwoTrace (fun t => Real.sqrt κ * B t ω) (γ ω)

 

structure RegularSLEPresentation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) where
  samples : Set Ω
  measurable_samples : MeasurableSet samples
  full_samples : ∀ᵐ ω ∂P, ω ∈ samples
  B : ℝ≥0 → samples → ℝ
  measurable_B : ∀ t, Measurable (B t)
  continuous_B : ∀ ω, Continuous (fun t => B t ω)
  zero_B : ∀ ω, B 0 ω = 0
  brownian : IsBrownianReal B (P.comap (Subtype.val : samples → Ω))
  G : samples → ℝ≥0 → ℂ → ℂ
  F : samples → ℝ≥0 → ℂ → ℂ
  witness : ∀ ω : samples, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
    (γ ω) (G ω) (F ω)

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

lemma measurePreserving_val (a : RegularSLEPresentation P κ γ) :
    MeasurePreserving (Subtype.val : a.samples → Ω) (P.comap Subtype.val) P := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe a.measurable_samples,
    Measure.restrict_eq_self_of_ae_mem a.full_samples]

instance probability [IsProbabilityMeasure P] (a : RegularSLEPresentation P κ γ) :
    IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) :=
  (MeasurableEmbedding.subtype_coe a.measurable_samples).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe] using a.full_samples)

def filtration (a : RegularSLEPresentation P κ γ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace a.samples) :=
  Filtration.natural a.B (fun t => (a.measurable_B t).stronglyMeasurable)

lemma trace_adapted (a : RegularSLEPresentation P κ γ) :
    Adapted a.filtration (fun t ω => γ ω t) := by
  apply capacity_trace_adapted a.filtration (fun t ω => Real.sqrt κ * a.B t ω)
    ?_ ?_ (γ ∘ Subtype.val) a.G a.F a.witness
  · intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (a.measurable_B t).stronglyMeasurable)) t).measurable
  · intro ω
    exact continuous_const.mul (a.continuous_B ω)

lemma trace_continuous (a : RegularSLEPresentation P κ γ) (ω : a.samples) :
    Continuous (γ ω) := (a.witness ω).1

end RegularSLEPresentation

 

theorem exists_regular_sle_presentation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) :
    Nonempty (RegularSLEPresentation P κ γ) := by
  classical
  obtain ⟨B, hB, htrace⟩ := hSLE.2
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have htraceC : ∀ᵐ ω ∂P, IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω) := by
    filter_upwards [htrace, hCB] with ω hω heq
    simpa only [heq] using hω
  let N := toMeasurable P {ω | ¬ IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω)}
  let S := Nᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hNa : P N = 0 := by
    rw [show N = toMeasurable P {ω | ¬ IsCapacityTwoTrace
      (fun t => Real.sqrt κ * C t ω) (γ ω)} from rfl, measure_toMeasurable]
    exact ae_iff.mp htraceC
  have hSa : ∀ᵐ ω ∂P, ω ∈ S := by
    apply ae_iff.mpr
    simpa only [S, mem_compl_iff, not_not, ofPred_mem_eq] using hNa
  have hw (ω : S) : IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω) := by
    by_contra hh
    exact ω.property (subset_toMeasurable P _ hh)
  choose G F hGF using hw
  have hval : MeasurePreserving (Subtype.val : S → Ω) (P.comap Subtype.val) P := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe hSm, Measure.restrict_eq_self_of_ae_mem hSa]
  refine ⟨{
    samples := S
    measurable_samples := hSm
    full_samples := hSa
    B := fun t ω => C t ω
    measurable_B := fun t => (hCm.comp (measurable_prodMk_left (x := t))).comp measurable_subtype_coe
    continuous_B := fun ω => hCc ω
    zero_B := fun ω => hC0 ω
    brownian := ?_
    G := G
    F := F
    witness := hGF }⟩
  exact ⟨⟨fun I => (hC.hasLaw I).comp hval.hasLaw⟩, Eventually.of_forall (fun ω => hCc ω)⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem ordinary_positive_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < (8-κ)/32 := by positivity
  have hδ2 : (8-κ)/32 ≤ 1/2 := by linarith
  have hβ : 0 < 3*(8-κ)/(4*κ) := by positivity
  by_cases hrx : r < ((8-κ)/32)*x
  · apply (measure_mono_ae (show {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤ᵐ[P]
      {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r ((8-κ)/32)} from ?_)).trans
      (boundary_comparison_failure_sle_exponent hB κ x r hκ hκ8 hx hr)
    filter_upwards [hw,hB.cont,hB.eval_zero_ae_eq_zero] with ω hω hc h0
    rintro ⟨t,ht⟩
    by_contra hn
    have hh := hω.all_time_real_center_avoidance (hc.const_mul _) (by simp only [h0,mul_zero])
      hx hrx hδ2 hn t
    exact (not_lt_of_ge hh) (by simpa only [dist_eq_norm] using ht)
  · have hq : 1 ≤ r/(((8-κ)/32)*x) :=
      (le_div_iff₀ (mul_pos hδ hx)).mpr (by simpa only [one_mul] using le_of_not_gt hrx)
    have hh := ENNReal.ofReal_le_ofReal (Real.one_le_rpow hq hβ.le)
    rw [ENNReal.ofReal_one] at hh
    exact prob_le_one.trans hh

 

theorem sle_positive_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  classical
  obtain ⟨B,hB,htrace⟩ := hSLE.2
  have hchoice (ω : Ω) : ∃ G F : ℝ≥0 → ℂ → ℂ,
      IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω) →
        IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) G F := by
    by_cases h : IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω)
    · obtain ⟨G,F,hw⟩ := h
      exact ⟨G,F,fun _ => hw⟩
    · exact ⟨fun _ _ => 0,fun _ _ => 0,fun hh => False.elim (h hh)⟩
  choose G F hw using hchoice
  exact ordinary_positive_real_center_approach hB κ hκ hκ8 γ G F
    (htrace.mono fun ω hω => hw ω hω) x r hx hr

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex ComplexConjugate
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsOrdinaryChordalSLE.mirror
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (h : IsOrdinaryChordalSLE κ γ P) :
    IsOrdinaryChordalSLE κ (fun ω => loewnerMirror ∘ γ ω) P := by
  obtain ⟨hm,B,hB,hw⟩ := h
  refine ⟨fun t => loewnerMirror.continuous.measurable.comp (hm t),-B,hB.neg,?_⟩
  filter_upwards [hw] with ω hω
  obtain ⟨G,F,hGF⟩ := hω
  refine ⟨fun t z => loewnerMirror (G t (loewnerMirror z)),
    fun t z => loewnerMirror (F t (loewnerMirror z)),?_⟩
  simpa only [Pi.neg_apply,mul_neg] using hGF.mirror

 
theorem sle_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (x r : ℝ) (hx : x ≠ 0) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*|x|))^(3*(8-κ)/(4*κ))) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hh := sle_positive_real_center_approach κ hκ hκ8
      (fun ω => loewnerMirror ∘ γ ω) hSLE.mirror (-x) r (neg_pos.mpr hx) hr
    have he : {ω | ∃ t : ℝ≥0, dist ((loewnerMirror ∘ γ ω) t) ((-x:ℝ):ℂ) < r} =
        {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} := by
      ext ω
      have hrx : ((-x:ℝ):ℂ) = loewnerMirror (x:ℂ) := by simp
      simp only [Function.comp_apply,hrx,loewnerMirror_dist]
    rw [he] at hh
    simpa only [abs_of_neg hx] using hh
  · simpa only [abs_of_pos hx] using
      sle_positive_real_center_approach κ hκ hκ8 γ hSLE x r hx hr

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma derivative_close_of_cauchy {f : ℂ → ℂ} {U : Set ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinc : closedBall b r ⊆ U)
    (hbound : ∀ w ∈ closedBall b r, ‖deriv f w‖ ≤ 2 * ‖deriv f b‖) :
    ∀ w ∈ closedBall b (r / 8), ‖deriv f w - deriv f b‖ ≤ ‖deriv f b‖ / 2 := by
  have hdr := hd.deriv hU
  have hsmall : closedBall b (r / 8) ⊆ closedBall b r := closedBall_subset_closedBall (by linarith)
  have hsecond (w : ℂ) (hw : w ∈ closedBall b (r / 8)) :
      ‖deriv (deriv f) w‖ ≤ 4 * ‖deriv f b‖ / r := by
    have hs : closedBall w (r / 2) ⊆ closedBall b r := by
      intro z hz
      apply mem_closedBall.mpr
      have hw' := mem_closedBall.mp hw
      have hz' := mem_closedBall.mp hz
      exact (dist_triangle z w b).trans (by linarith)
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 2)
      (hdr.diffContOnCl_ball (hs.trans hinc))
      (fun z hz => hbound z (hs (sphere_subset_closedBall hz)))
    convert hh using 1
    ring
  intro w hw
  have hh := (convex_closedBall b (r / 8)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hdr.differentiableAt (hU.mem_nhds (hinc (hsmall hz)))) hsecond
    (mem_closedBall_self (by positivity : 0 ≤ r / 8)) hw
  have hn : ‖w - b‖ ≤ r / 8 := mem_closedBall_iff_norm.mp hw
  calc
    ‖deriv f w - deriv f b‖ ≤ (4 * ‖deriv f b‖ / r) * ‖w - b‖ := hh
    _ ≤ (4 * ‖deriv f b‖ / r) * (r / 8) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖deriv f b‖ / 2 := by field_simp; ring

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma disk_image_of_deriv_close {f f' : ℂ → ℂ} {b a : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : a ≠ 0)
    (hd : ∀ z ∈ closedBall b r, HasDerivAt f (f' z) z)
    (hb : ∀ z ∈ closedBall b r, ‖f' z / a - 1‖ ≤ 1 / 2) :
    closedBall (f b) (‖a‖ * r / 2) ⊆ f '' closedBall b r := by
  let g : ℂ → ℂ := fun z => f z / a
  have hl : LipschitzOnWith (1 / 2 : ℝ≥0) (fun z => g z - z) (closedBall b r) := by
    apply (convex_closedBall b r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun z => f' z / a - 1)
    · intro z hz
      exact (((hd z hz).div_const a).sub (hasDerivAt_id z)).hasDerivWithinAt
    · intro z hz
      exact_mod_cast hb z hz
  have hl' : ApproximatesLinearOn g (ContinuousLinearMap.id ℂ ℂ) (closedBall b r) (1 / 2) := by
    apply LipschitzOnWith.approximatesLinearOn
    exact hl
  have hs := hl'.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse hr (Subset.refl _)
  have hs' : SurjOn g (closedBall b r) (closedBall (g b) (r / 2)) := by
    norm_num [ContinuousLinearEquiv.toNonlinearRightInverse] at hs
    convert hs using 1
    ring_nf
  intro y hy
  have hy' : y / a ∈ closedBall (g b) (r / 2) := by
    rw [mem_closedBall_iff_norm] at hy ⊢
    change ‖y / a - f b / a‖ ≤ r / 2
    rw [← sub_div, norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr ha)).mpr
    nlinarith
  obtain ⟨z, hz, he⟩ := hs' hy'
  exact ⟨z, hz, (div_left_inj' ha).mp he⟩

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma bloch_disk {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1)) :
    ∃ b ∈ ball (0 : ℂ) 1,
      closedBall (f b) (‖deriv f 0‖ / 64) ⊆ f '' ball 0 1 := by
  have hzero : (0 : ℂ) ∈ closedBall 0 (1 / 2 : ℝ) := mem_closedBall_self (by norm_num)
  have hinc : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  by_cases h0 : deriv f 0 = 0
  · refine ⟨0, mem_ball_self (by norm_num), ?_⟩
    simp only [h0, norm_zero, zero_div, closedBall_zero, singleton_subset_iff]
    exact mem_image_of_mem f (mem_ball_self (by norm_num))
  have hd0 : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr h0
  let Φ : ℂ → ℝ := fun z => (1 / 2 - ‖z‖) * ‖deriv f z‖
  have hc : ContinuousOn Φ (closedBall 0 (1 / 2 : ℝ)) :=
    (continuousOn_const.sub continuous_norm.continuousOn).mul
      ((hd.deriv isOpen_ball).continuousOn.mono hinc).norm
  obtain ⟨b, hb, hmax⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)).exists_isMaxOn
    ⟨0, hzero⟩ hc
  have hM : ‖deriv f 0‖ / 2 ≤ (1 / 2 - ‖b‖) * ‖deriv f b‖ := by
    have hh := hmax hzero
    simpa [Φ, norm_zero, mul_comm, div_eq_mul_inv] using hh
  have hb' : ‖b‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hb
  have hab : 0 < ‖deriv f b‖ := by
    by_contra hn
    have hh : ‖deriv f b‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [hh, mul_zero] at hM
    linarith
  have hmargin : 0 < 1 / 2 - ‖b‖ := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hab.le
    linarith
  let r : ℝ := (1 / 2 - ‖b‖) / 2
  have hr : 0 < r := div_pos hmargin (by norm_num)
  have hsub : closedBall b r ⊆ closedBall 0 (1 / 2 : ℝ) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hw' : ‖w - b‖ ≤ r := mem_closedBall_iff_norm.mp hw
    have hnorm : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert b w
    dsimp [r] at hw'
    linarith
  have hbound (w : ℂ) (hw : w ∈ closedBall b r) : ‖deriv f w‖ ≤ 2 * ‖deriv f b‖ := by
    have hh := hmax (hsub hw)
    change (1 / 2 - ‖w‖) * ‖deriv f w‖ ≤ (1 / 2 - ‖b‖) * ‖deriv f b‖ at hh
    have hw' : ‖w - b‖ ≤ r := mem_closedBall_iff_norm.mp hw
    have hnorm : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert b w
    have hm : r ≤ 1 / 2 - ‖w‖ := by dsimp [r] at *; linarith
    have he : 1 / 2 - ‖b‖ = 2 * r := by dsimp [r]; ring
    have hprod := mul_le_mul_of_nonneg_right hm (norm_nonneg (deriv f w))
    rw [he] at hh
    nlinarith
  have hclose := derivative_close_of_cauchy hr isOpen_ball hd (hsub.trans hinc) hbound
  have hsmall : closedBall b (r / 8) ⊆ closedBall b r := closedBall_subset_closedBall (by linarith)
  have himage := disk_image_of_deriv_close (f := f) (f' := deriv f) (a := deriv f b)
    (by positivity : 0 ≤ r / 8) (norm_pos_iff.mp hab)
    (fun w hw => (hd.differentiableAt (isOpen_ball.mem_nhds (hinc (hsub (hsmall hw))))).hasDerivAt)
    (by
      intro w hw
      rw [← div_self (norm_pos_iff.mp hab), ← sub_div, norm_div]
      exact (div_le_iff₀ hab).mpr (by simpa [div_eq_mul_inv, mul_comm] using hclose w hw))
  refine ⟨b, hinc hb, ?_⟩
  have hlower : ‖deriv f 0‖ / 64 ≤ ‖deriv f b‖ * (r / 8) / 2 := by
    dsimp [r]
    nlinarith
  exact (closedBall_subset_closedBall hlower).trans
    (himage.trans (image_mono (hsmall.trans (hsub.trans hinc))))

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma hasDerivAt_log_lift {g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hh : ContinuousOn h U)
    (he : EqOn (Complex.exp ∘ h) g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt h (deriv g z / g z) z := by
  have hgz : g z ≠ 0 := by rw [← he hz]; exact Complex.exp_ne_zero _
  have hdz := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hcx := hh.continuousAt (hU.mem_nhds hz)
  have hdisc : ∀ᶠ w in 𝓝 z, ‖h w - h z‖ < Real.pi := by
    have hc : ContinuousAt (fun w => ‖h w - h z‖) z := (hcx.sub continuousAt_const).norm
    exact hc (Iio_mem_nhds (by simpa using Real.pi_pos))
  have hlocal : (fun w => Complex.log (g w / g z) + h z) =ᶠ[𝓝 z] h := by
    filter_upwards [hU.mem_nhds hz, hdisc] with w hw hw'
    have him : |(h w - h z).im| < Real.pi := (Complex.abs_im_le_norm _).trans_lt hw'
    rw [← he hw, ← he hz]
    change Complex.log (Complex.exp (h w) / Complex.exp (h z)) + h z = h w
    rw [← Complex.exp_sub, Complex.log_exp (by linarith [(abs_lt.mp him).1])
      (le_of_lt (abs_lt.mp him).2)]
    ring
  have hlog := (hdz.div_const (g z)).clog (by simp [hgz])
  have hf : HasDerivAt (fun w => Complex.log (g w / g z) + h z) (deriv g z / g z) z := by
    simpa [hgz] using hlog.add_const (h z)
  exact hf.congr_of_eventuallyEq hlocal.symm

lemma differentiableOn_log_lift {g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hh : ContinuousOn h U)
    (he : EqOn (Complex.exp ∘ h) g U) : DifferentiableOn ℂ h U :=
  fun _ hz => (hasDerivAt_log_lift hU hg hh he hz).differentiableAt.differentiableWithinAt

lemma exists_holomorphic_log_on_ball {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (ball b r))
    (h0 : ∀ z ∈ ball b r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball b r) ∧
      EqOn (Complex.exp ∘ h) g (ball b r) ∧
      ∀ z ∈ ball b r, deriv h z = deriv g z / g z := by
  let := (convex_ball b r).contractibleSpace ⟨b, mem_ball_self hr⟩
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (by change SimplyConnectedSpace (ball b r); infer_instance) isOpen_ball hg.continuousOn
    (by rintro ⟨z, hz, he⟩; exact h0 z hz he)
  exact ⟨h, differentiableOn_log_lift isOpen_ball hg hh he, he,
    fun z hz => (hasDerivAt_log_lift isOpen_ball hg hh he hz).deriv⟩

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma univalent_omitted_value_bound {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (a : ℂ) (ha : a ∉ f '' ball 0 1) :
    ‖deriv f 0‖ ≤ (128 * Real.pi) * ‖f 0 - a‖ := by
  have hnon (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz, sub_eq_zero.mp he⟩
  have hz0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  obtain ⟨h, hhd, he, hhder⟩ := exists_holomorphic_log_on_ball (by norm_num : (0 : ℝ) < 1)
    (hd.sub_const a) hnon
  obtain ⟨b, hb, hball⟩ := bloch_disk hhd
  have hbound : ‖deriv h 0‖ < 128 * Real.pi := by
    by_contra hn
    have hn' : 128 * Real.pi ≤ ‖deriv h 0‖ := le_of_not_gt hn
    have hw : h b + 2 * Real.pi * Complex.I ∈ closedBall (h b) (‖deriv h 0‖ / 64) := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_mul, norm_mul,
        norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      linarith
    obtain ⟨z, hz, hzh⟩ := hball hw
    have hfe : f z - a = f b - a := by
      calc
        f z - a = Complex.exp (h z) := (he hz).symm
        _ = Complex.exp (h b) := by rw [hzh]; exact Complex.exp_periodic (h b)
        _ = f b - a := he hb
    have hzb : z = b := hi hz hb (sub_left_inj.mp hfe)
    rw [hzb] at hzh
    have him := congrArg Complex.im hzh
    norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re] at him
  have hd0 := (hd.differentiableAt (isOpen_ball.mem_nhds hz0)).hasDerivAt
  have hdsub : deriv (fun z => f z - a) 0 = deriv f 0 := (hd0.sub_const a).deriv
  rw [hhder 0 hz0, hdsub, norm_div] at hbound
  exact ((div_lt_iff₀ (norm_pos_iff.mpr (hnon 0 hz0))).mp hbound).le

end SLEExactGauge
end

 
end

end OAI
