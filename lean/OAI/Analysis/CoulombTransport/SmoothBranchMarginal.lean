import OAI.Analysis.CoulombTransport.Density
import OAI.Analysis.CoulombTransport.DisjointSquares
import OAI.Analysis.CoulombTransport.SmoothPushforward
import OAI.Analysis.CoulombTransport.LocalBranchMeasure
import OAI.Analysis.CoulombTransport.JacobianSquareRoot

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.SmoothBranchMarginal

theorem squareDensity_probability {g : E3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hmass : (∫ x : E3, g x ^ 2) = 1) :
    IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) := by
  have hcompact : HasCompactSupport (fun x => g x ^ 2) := by
    simpa only [Function.comp_def] using
      hgc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint : Integrable (fun x => g x ^ 2) (volume : Measure E3) :=
    (hg.pow 2).integrable_of_hasCompactSupport hcompact
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => sq_nonneg (g x))),
    hmass, ENNReal.ofReal_one]

theorem squareDensity_ae_tsupport {g : E3 → ℝ} (hg : Measurable g) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ tsupport g := by
  rw [densityMeasure, ae_withDensity_iff ((hg.pow_const 2).ennreal_ofReal)]
  apply ae_of_all
  intro x hx
  apply subset_tsupport g
  intro hgx
  exact hx (by simp [hgx])

theorem square_integral_eq_one {g : E3 → ℝ} (hg : Continuous g)
    [IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2))] :
    (∫ x : E3, g x ^ 2) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => sq_nonneg (g x))) (hg.pow 2).aestronglyMeasurable]
  have hm := measure_univ (μ := densityMeasure (fun x => g x ^ 2))
  simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hm, ENNReal.toReal_one] using congrArg ENNReal.toReal hm

/-- A normalized smooth amplitude transports to another normalized smooth
amplitude. The derivative and its smooth square-root determinant are explicit
inputs, so the result is compatible with independently constructed local charts. -/
theorem transported_square_amplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ e.source)
    (hmass : (∫ x : E3, g x ^ 2) = 1)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y)
    (hJ : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D y).det|) e.target) :
    ∃ q : E3 → ℝ,
      (∀ y, 0 ≤ q y) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q ∧
      HasCompactSupport q ∧
      tsupport q ⊆ e '' tsupport g ∧
      (∫ y : E3, q y ^ 2) = 1 ∧
      Measure.map (LocalBranchMeasure.extendedBranch e 0)
        (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
  let q := localTransportAmplitude e g (fun y => Real.sqrt |(D y).det|)
  have hq : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q :=
    contDiff_localTransportAmplitude e hg hgc hgs he hJ
  have hm : Measure.map (LocalBranchMeasure.extendedBranch e 0)
      (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
    rw [LocalBranchMeasure.map_extendedBranch e 0 _
      ((squareDensity_ae_tsupport hg.continuous.measurable).mono (fun x hx => hgs hx))]
    exact map_squareDensity_localHomeomorph e g hgs D hD
  have := squareDensity_probability hg.continuous hgc hmass
  have : IsProbabilityMeasure (densityMeasure (fun y => q y ^ 2)) := by
    rw [← hm]
    infer_instance
  refine ⟨q, localTransportAmplitude_nonneg e hg0 (fun y _ => Real.sqrt_nonneg _), hq,
    hasCompactSupport_localTransportAmplitude e _ hgc hgs,
    tsupport_localTransportAmplitude_subset e _ hgc hgs, ?_, hm⟩
  exact square_integral_eq_one hq.continuous

/-- The five component weights are fixed by the counterexample construction. -/
def componentWeight : Option (Fin 4) → ℝ
  | none => 1 / 3
  | some _ => 1 / 6

def componentAmplitude (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) :
    Option (Fin 4) → E3 → ℝ
  | none => g
  | some i => q i

def componentRegion (B : Set E3) (e : Fin 4 → OpenPartialHomeomorph E3 E3) :
    Option (Fin 4) → Set E3
  | none => B
  | some i => e i '' B

def marginalDensity (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i : Option (Fin 4), componentWeight i * componentAmplitude g q i x ^ 2

def NormalizedAmplitude (g : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧
  ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
  HasCompactSupport g ∧ (∫ x : E3, g x ^ 2) = 1

theorem marginalDensity_smooth {B : Set E3}
    {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : NormalizedAmplitude g) (hq : ∀ i, NormalizedAmplitude (q i))
    (hgs : tsupport g ⊆ B) (hqs : ∀ i, tsupport (q i) ⊆ e i '' B)
    (hdisj : Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j))) :
    IsSmoothCompactProbabilityDensity (marginalDensity g q) := by
  apply isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    Finset.univ componentWeight (componentAmplitude g q)
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg.1
    | some i => exact (hq i).1
  · intro i _
    cases i with
    | none => exact hg.2.1
    | some i => exact (hq i).2.1
  · intro i _
    cases i with
    | none => exact hg.2.2.1
    | some i => exact (hq i).2.2.1
  · have hsub : ∀ i, Function.support (componentAmplitude g q i) ⊆ componentRegion B e i := by
      intro i
      cases i with
      | none => exact (subset_tsupport g).trans hgs
      | some i => exact (subset_tsupport (q i)).trans (hqs i)
    intro i _ j _ hij
    exact (hdisj hij).mono (hsub i) (hsub j)
  · intro i _
    cases i with
    | none => exact hg.2.2.2
    | some i => exact (hq i).2.2.2
  · norm_num [componentWeight, Fintype.sum_option]

theorem marginalDensity_measure {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : Measurable g) (hq : ∀ i, Measurable (q i)) :
    densityMeasure (marginalDensity g q) =
      (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
      ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • densityMeasure (fun x => q i x ^ 2) := by
  unfold marginalDensity
  rw [densityMeasure_sum_weighted_squares]
  · simp [Fintype.sum_option, componentWeight, componentAmplitude]
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg
    | some i => exact hq i

/-- Construct the actual smooth five-component marginal from local branch
charts on a common ball. All square amplitudes and their exact pushforward
laws are supplied in the conclusion. -/
theorem exists_smooth_branch_marginal
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    (D : Fin 4 → E3 → E3 →L[ℝ] E3)
    (hD : ∀ i y, y ∈ (e i).target → HasFDerivAt (e i).symm (D i y) y)
    (hJ : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D i y).det|) (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  obtain ⟨g, hg0, hg, hgc, hgs, hgm⟩ := exists_normalized_smooth_square_in_ball c hr
  have hqexists := fun i => transported_square_amplitude (e i) hg0 hg hgc
    (hgs.trans (hsource i)) hgm (he i) (D i) (hD i) (hJ i)
  choose q hq0 hq hqc hqs hqm hqmap using hqexists
  have hgn : NormalizedAmplitude g := ⟨hg0, hg, hgc, hgm⟩
  have hqn : ∀ i, NormalizedAmplitude (q i) := fun i => ⟨hq0 i, hq i, hqc i, hqm i⟩
  have hqsub : ∀ i, tsupport (q i) ⊆ e i '' Metric.ball c r := fun i =>
    (hqs i).trans (Set.image_mono hgs)
  refine ⟨g, q, hgn, hgs, fun i => ⟨hqn i, hqsub i⟩,
    squareDensity_probability hg.continuous hgc hgm,
    marginalDensity_smooth hgn hqn hgs hqsub hdisj, ?_⟩
  rw [marginalDensity_measure hg.continuous.measurable (fun i => (hq i).continuous.measurable)]
  simp_rw [hqmap]

/-- The preceding construction only needs smoothness in both directions of
the local charts; no determinant or change-of-variables premise remains. -/
theorem exists_smooth_branch_marginal_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  apply exists_smooth_branch_marginal c hr e hsource hdisj he'
    (fun i y => fderiv ℝ (e i).symm y)
  · intro i y hy
    exact (((he' i).contDiffAt ((e i).open_target.mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt
  · intro i
    exact JacobianSquareRoot.contDiffOn_sqrt_abs_det_fderiv_symm (e i) (he i) (he' i)

/-- The construction data expected by the measure-level nonattainment and
separated-support approximation arguments. -/
structure SmoothBranchData (B : Set E3) where
  rho : E3 → ℝ
  nu : Measure E3
  branch : Fin 4 → E3 → E3
  compactCore : Set E3
  density_smooth : IsSmoothCompactProbabilityDensity rho
  probability : IsProbabilityMeasure nu
  measurable_central : MeasurableSet B
  core_compact : IsCompact compactCore
  core_subset : compactCore ⊆ B
  core_full : ∀ᵐ x ∂nu, x ∈ compactCore
  branch_measurable : ∀ i, Measurable (branch i)
  branch_injective : ∀ i, Set.InjOn (branch i) B
  branch_image_measurable : ∀ i S, MeasurableSet S → S ⊆ B →
    MeasurableSet (branch i '' S)
  branch_continuous : ∀ i, ContinuousOn (branch i) compactCore
  component_disjoint : Pairwise (fun i j : Option (Fin 4) =>
    Disjoint (i.elim B (fun k => branch k '' B)) (j.elim B (fun k => branch k '' B)))
  density_eq : densityMeasure rho =
    (1 / 3 : ℝ≥0∞) • nu + ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • Measure.map (branch i) nu

theorem SmoothBranchData.central_full {B : Set E3} (d : SmoothBranchData B) :
    ∀ᵐ x ∂d.nu, x ∈ B := d.core_full.mono (fun _ hx => d.core_subset hx)

theorem SmoothBranchData.central_disjoint {B : Set E3} (d : SmoothBranchData B) (i : Fin 4) :
    Disjoint B (d.branch i '' B) :=
  d.component_disjoint (i := none) (j := some i) (by simp)

theorem SmoothBranchData.outer_disjoint {B : Set E3} (d : SmoothBranchData B) :
    Pairwise (fun i j => Disjoint (d.branch i '' B) (d.branch j '' B)) := by
  intro i j hij
  exact d.component_disjoint (i := some i) (j := some j) (by simpa using hij)

/-- The explicit four-term form is definitionally the canonical branch marginal. -/
theorem SmoothBranchData.density_eq_four {B : Set E3} (d : SmoothBranchData B) :
    densityMeasure d.rho = (1 / 3 : ℝ≥0∞) • d.nu + (1 / 6 : ℝ≥0∞) •
      (Measure.map (d.branch 0) d.nu + Measure.map (d.branch 1) d.nu +
        Measure.map (d.branch 2) d.nu + Measure.map (d.branch 3) d.nu) := by
  rw [d.density_eq]
  simp [Fin.sum_univ_succ, smul_add, add_assoc]

/-- A measure-level packaging of the actual smooth marginal construction.
All branch extensions are globally measurable, while continuity is retained
on the compact support where it is needed. -/
theorem exists_smoothBranchData_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ d : SmoothBranchData (Metric.ball c r),
      ∀ i x, x ∈ Metric.ball c r → d.branch i x = e i x := by
  obtain ⟨g, q, hg, hgs, _, hprob, hrho, hmeasure⟩ :=
    exists_smooth_branch_marginal_of_smooth_charts c hr e hsource hdisj he he'
  let H : Fin 4 → E3 → E3 := fun i => LocalBranchMeasure.extendedBranch (e i) 0
  have himage : ∀ i, H i '' Metric.ball c r = e i '' Metric.ball c r :=
    fun i => LocalBranchMeasure.extendedBranch_image (e i) 0 (hsource i)
  refine ⟨{
    rho := marginalDensity g q
    nu := densityMeasure (fun x => g x ^ 2)
    branch := H
    compactCore := tsupport g
    density_smooth := hrho
    probability := hprob
    measurable_central := Metric.isOpen_ball.measurableSet
    core_compact := hg.2.2.1
    core_subset := hgs
    core_full := squareDensity_ae_tsupport hg.2.1.continuous.measurable
    branch_measurable := fun i => LocalBranchMeasure.measurable_extendedBranch (e i) 0
    branch_injective := fun i => LocalBranchMeasure.injOn_extendedBranch (e i) 0 (hsource i)
    branch_image_measurable := ?_
    branch_continuous := ?_
    component_disjoint := ?_
    density_eq := hmeasure
  }, ?_⟩
  · intro i S hS hSB
    exact LocalBranchMeasure.measurableSet_extendedBranch_image (e i) 0 hS
      (hSB.trans (hsource i))
  · intro i
    apply ((e i).continuousOn.mono (hgs.trans (hsource i))).congr
    intro x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i (hgs hx))
  · intro i j hij
    have h := hdisj hij
    cases i <;> cases j <;> simpa only [Option.elim, componentRegion, himage] using h
  · intro i x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i hx)

end Problem356.SmoothBranchMarginal

end

end OAI
