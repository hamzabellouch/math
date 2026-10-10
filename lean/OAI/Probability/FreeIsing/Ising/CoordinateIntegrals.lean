import OAI.Probability.FreeIsing.Estimates.CoefficientTerminalCompletion
import OAI.Probability.FreeIsing.Ising.InnovationIndependence
import OAI.Probability.FreeIsing.Ising.MixedFiltering

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma posterior_memLp
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (P : Measure (State d A)) [IsFiniteMeasure P] (v : TreeVertex d) (T : ℝ≥0) :
    MemLp (posterior beta B v T) 2 P := by
  apply MemLp.of_bound
    ((measurable_posterior_joint beta B hmB hcB v).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Prod.fst, Prod.snd, id_eq] using
      posterior_abs_le_one beta B v T q

lemma finiteCovariance_memLp
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (P : Measure (State d A)) [IsFiniteMeasure P]
    (v u : TreeVertex d) (n : ℕ) (t : ℝ≥0) :
    MemLp (finiteCovariance beta B v u n t) 2 P := by
  apply MemLp.of_bound
    (((finiteCovariance_stronglyAdapted beta B hmB v u n) t).mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t)).aestronglyMeasurable 2
  exact Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using finiteCovariance_abs_le_two beta B v u n t q

theorem exists_finiteCovariance_integrals
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ X : ℕ → TreeVertex d → State d A → ℝ,
      (∀ n u, StronglyMeasurable[F T] (X n u)) ∧
      (∀ n u, MemLp (X n u) 2 P) ∧
      (∀ n u, (∫ q, X n u q ∂P) = 0) ∧
      (∀ n u, Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          T k q - X n u q) ^ 2 ∂P) atTop (𝓝 0)) := by
  classical
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hex (n : ℕ) (u : TreeVertex d) :=
    BrownianFiltrationGrid.exists_terminal_uniform_integral_of_bounded_continuous
      (isBrownianReal_innovation hμ ν hB hmB hcB u).toIsPreBrownianReal
      (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (innovation_increment_indep_filtration hμ ν hB hmB hcB s t hst) u)
      (finiteCovariance beta B v u n) (finiteCovariance_stronglyAdapted beta B hmB v u n)
      (Eventually.of_forall (finiteCovariance_continuous beta B hcB v u n))
      (show (0 : ℝ) ≤ 2 by norm_num)
      (Eventually.of_forall (fun q t => finiteCovariance_abs_le_two beta B v u n t q)) T
  choose X htX hX hzX haX using hex
  exact ⟨X, htX, hX, hzX, haX⟩

lemma interval_integral_eq_timeSpace
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (T : ℝ≥0) {f : ℝ × Ω → ℝ}
    (hf : Integrable f ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P)) :
    (∫ r in (0 : ℝ)..(T : ℝ), ∫ q, f (r, q) ∂P) =
      ∫ p, f p ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (integral_prod f hf).symm

theorem finiteCovariance_integral_cross
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (n : ℕ) (T : ℝ≥0) {X : State d A → ℝ}
    (hX : MemLp X 2 (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (haX : Tendsto (fun k => ∫ q,
      (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
        T k q - X q) ^ 2 ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      atTop (𝓝 0)) :
    (∫ q, posterior beta B v T q * X q
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
    ∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
      finiteCovariance beta B v u n r.toNNReal q * covariance beta B v u r.toNNReal q
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply FilteringRepresentationClosure.integral_mul_eq_of_meanSquare_limit
    (posterior_memLp beta B hmB hcB _ v T) hX _ haX
    (tendsto_finiteCovariance_cross_uniformSum hμ ν hB hmB hcB v u n T)
  exact BrownianFiltrationGrid.uniformSum_memLp
    (isBrownianReal_innovation hμ ν hB hmB hcB u).toIsPreBrownianReal
    (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
    (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
      (innovation_increment_indep_filtration hμ ν hB hmB hcB s t hst) u)
    (finiteCovariance beta B v u n) (finiteCovariance_stronglyAdapted beta B hmB v u n)
    (finiteCovariance_memLp beta B hmB _ v u n) T

theorem finiteCovariance_integrals_orthogonal
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (n : ℕ) (T : ℝ≥0) {X : TreeVertex d → State d A → ℝ}
    (hX : ∀ u, MemLp (X u) 2 (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (haX : ∀ u, Tendsto (fun k => ∫ q,
      (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
        T k q - X u q) ^ 2 ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      atTop (𝓝 0)) :
    Pairwise fun u w => ∫ q, X u q * X w q
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) = 0 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply BrownianArrayFiltration.uniform_meanSquare_limits_orthogonal
    (fun u => (isBrownianReal_innovation hμ ν hB hmB hcB u).toIsPreBrownianReal)
    (fun u => (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted)
    (innovation_increment_indep_filtration hμ ν hB hmB hcB) _
    (fun u => finiteCovariance beta B v u n)
    (fun u => finiteCovariance_stronglyAdapted beta B hmB v u n)
    (fun u => finiteCovariance_memLp beta B hmB _ v u n) T hX haX
  intro s t hst u w huw
  exact (innovation_increment_law_and_indep hμ ν hB hmB hcB
    (Y := fun _ => ()) s t hst measurable_const).2.1.indepFun huw

end Problem367.IsingInnovation

end

end OAI
