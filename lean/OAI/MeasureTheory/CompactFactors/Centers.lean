import Mathlib

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace EuclideanFiveColor.Location

abbrev Ambient := WithLp 2 (ℝ × ℂ)

def lift (z : ℂ) : Ambient := WithLp.toLp 2 (1, z)

@[simp] theorem lift_fst (z : ℂ) : (lift z).fst = 1 := rfl
@[simp] theorem lift_snd (z : ℂ) : (lift z).snd = z := rfl

theorem lift_ne_zero (z : ℂ) : lift z ≠ 0 := by
  intro h
  have := congrArg WithLp.fst h
  simp at this

theorem norm_lift (z : ℂ) : ‖lift z‖ = Real.sqrt (1 + ‖z‖ ^ 2) := by
  simp [WithLp.prod_norm_eq_of_L2]

theorem lift_sub (z w : ℂ) : lift z - lift w = WithLp.toLp 2 (0, z - w) := by
  apply WithLp.ofLp_injective 2
  simp [lift]

theorem norm_lift_sub (z w : ℂ) : ‖lift z - lift w‖ = ‖z - w‖ := by
  rw [lift_sub, WithLp.norm_toLp_snd]

theorem lift_affine (z w : ℂ) (a b : ℝ) (hab : a + b = 1) :
    lift (a • z + b • w) = a • lift z + b • lift w := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simpa using hab.symm
  · rfl

theorem not_sameRay_smul_lift {z w : ℂ} (hzw : z ≠ w)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ SameRay ℝ (a • lift z) (b • lift w) := by
  intro h
  have haz : a • lift z ≠ 0 := smul_ne_zero ha.ne' (lift_ne_zero z)
  have hbw : b • lift w ≠ 0 := smul_ne_zero hb.ne' (lift_ne_zero w)
  obtain ⟨r, hr, he⟩ := h.exists_pos_left haz hbw
  have hfst := congrArg WithLp.fst he
  have hsnd := congrArg WithLp.snd he
  simp only [WithLp.smul_fst, lift_fst, smul_eq_mul, mul_one] at hfst
  simp only [WithLp.smul_snd, lift_snd, smul_smul, hfst] at hsnd
  exact hzw ((smul_right_injective ℂ hb.ne') hsnd)

theorem strictConvex_norm_lift : StrictConvexOn ℝ Set.univ (fun z : ℂ => ‖lift z‖) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  change ‖lift (a • z + b • w)‖ < a • ‖lift z‖ + b • ‖lift w‖
  rw [lift_affine z w a b hab]
  have := norm_add_lt_of_not_sameRay (not_sameRay_smul_lift hzw ha hb)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb,
    smul_eq_mul] using this

noncomputable def kernel (s t : ℂ) : ℝ := ‖lift (s - t)‖ - ‖lift (-t)‖

noncomputable def objective (μ : Measure ℂ) (s : ℂ) : ℝ := ∫ t, kernel s t ∂μ

theorem kernel_formula (s t : ℂ) : kernel s t =
    Real.sqrt (1 + ‖s - t‖ ^ 2) - Real.sqrt (1 + ‖t‖ ^ 2) := by
  simp [kernel, norm_lift]

theorem continuous_kernel (s : ℂ) : Continuous (kernel s) := by
  simp only [funext (kernel_formula s)]
  fun_prop

theorem kernel_bound (s t : ℂ) : |kernel s t| ≤ ‖s‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (-t))
  simpa [kernel, norm_lift_sub] using h

theorem kernel_diff_bound (s s' t : ℂ) : |kernel s t - kernel s' t| ≤ ‖s - s'‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (s' - t))
  simpa [kernel, norm_lift_sub, sub_sub_sub_cancel_right] using h

theorem integrable_kernel (μ : Measure ℂ) [IsFiniteMeasure μ] (s : ℂ) :
    Integrable (kernel s) μ := by
  apply (integrable_const ‖s‖).mono' (continuous_kernel s).aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa using kernel_bound s t

theorem objective_zero (μ : Measure ℂ) : objective μ 0 = 0 := by
  simp [objective, kernel]

theorem objective_lipschitz (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (objective μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s s'
  rw [Real.dist_eq, objective, objective, ← integral_sub (integrable_kernel μ s)
    (integrable_kernel μ s')]
  calc
    |∫ t, kernel s t - kernel s' t ∂μ| ≤ ∫ t, |kernel s t - kernel s' t| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℂ, ‖s - s'‖ ∂μ := by
      apply integral_mono ((integrable_kernel μ s).sub (integrable_kernel μ s')).abs
        (integrable_const _)
      exact fun t => kernel_diff_bound s s' t
    _ = (1 : ℝ≥0) * dist s s' := by simp [dist_eq_norm]

theorem continuous_objective (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Continuous (objective μ) := (objective_lipschitz μ).continuous

theorem kernel_strict_convex (t : ℂ) : StrictConvexOn ℝ Set.univ (fun s => kernel s t) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  have hn : z - t ≠ w - t := sub_left_injective.ne hzw
  have h := strictConvex_norm_lift.2 (Set.mem_univ (z - t))
    (Set.mem_univ (w - t)) hn ha hb hab
  have ht : a • t + b • t = t := by rw [← add_smul, hab, one_smul]
  have he : a • (z - t) + b • (w - t) = a • z + b • w - t := by
    calc
      _ = a • z + b • w - (a • t + b • t) := by
        simp only [smul_sub]
        abel
      _ = _ := by rw [ht]
  dsimp only at h
  rw [he] at h
  dsimp only [kernel]
  simp only [smul_eq_mul] at h ⊢
  have hc : a * ‖lift (-t)‖ + b * ‖lift (-t)‖ = ‖lift (-t)‖ := by
    rw [← add_mul, hab, one_mul]
  nlinarith only [h, hc]

theorem objective_strict_convex (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    StrictConvexOn ℝ Set.univ (objective μ) := by
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw hzw a b ha hb hab
  have hk (t : ℂ) := (kernel_strict_convex t).2 hz hw hzw ha hb hab
  have hf := integrable_kernel μ (a • z + b • w)
  have hg := ((integrable_kernel μ z).smul a).add ((integrable_kernel μ w).smul b)
  change (∫ t, kernel (a • z + b • w) t ∂μ) <
    a • (∫ t, kernel z t ∂μ) + b • (∫ t, kernel w t ∂μ)
  rw [← integral_smul, ← integral_smul, ← integral_add]
  · refine lt_of_le_of_ne (integral_mono hf hg fun t => (hk t).le) ?_
    intro he
    have heq := (integral_eq_iff_of_ae_le hf hg
      (Eventually.of_forall fun t => (hk t).le)).mp he
    obtain ⟨t, ht⟩ := heq.exists
    exact (hk t).ne ht
  · exact (integrable_kernel μ z).smul a
  · exact (integrable_kernel μ w).smul b

theorem norm_lift_le (z : ℂ) : ‖lift z‖ ≤ ‖z‖ + 1 := by
  calc
    ‖lift z‖ ≤ ‖lift z - lift 0‖ + ‖lift 0‖ := norm_le_norm_sub_add _ _
    _ = ‖z‖ + 1 := by simp [norm_lift_sub, norm_lift]

theorem kernel_lower (s t : ℂ) : ‖s‖ - 2 * ‖t‖ - 1 ≤ kernel s t := by
  have hst : ‖s - t‖ ≤ ‖lift (s - t)‖ := WithLp.norm_snd_le ℝ (lift (s - t))
  have hs : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := norm_le_norm_sub_add _ _
  have ht := norm_lift_le (-t)
  simp only [norm_neg] at ht
  dsimp only [kernel]
  linarith

theorem exists_ball_mass (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃ n : ℕ, (1 / 2 : ℝ) < μ.real (Metric.closedBall 0 (n : ℝ)) := by
  by_contra! h
  have hm (n : ℕ) : μ (Metric.closedBall 0 (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
    simpa [measureReal_def] using h n
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.mpr ⟨n, by simpa [Metric.mem_closedBall] using hn.le⟩
  have hmono : Monotone (fun n : ℕ => Metric.closedBall (0 : ℂ) (n : ℝ)) := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij)
  have he : μ (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hm
  rw [hc, measure_univ] at he
  norm_num at he

theorem objective_lower (μ : Measure ℂ) [IsProbabilityMeasure μ] (R : ℝ) (s : ℂ) :
    (2 * μ.real (Metric.closedBall 0 R) - 1) * ‖s‖ -
        μ.real (Metric.closedBall 0 R) * (2 * R + 1) ≤ objective μ s := by
  classical
  let B := Metric.closedBall (0 : ℂ) R
  let v := 2 * ‖s‖ - (2 * R + 1)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hi : Integrable (B.indicator (fun _ : ℂ => v)) μ :=
    (integrable_const v).indicator hB
  have hp (t : ℂ) : -‖s‖ + B.indicator (fun _ : ℂ => v) t ≤ kernel s t := by
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      have ht' : ‖t‖ ≤ R := by simpa [B, Metric.mem_closedBall] using ht
      have hlo := kernel_lower s t
      dsimp only [v]
      linarith
    · rw [Set.indicator_of_notMem ht, add_zero]
      exact (abs_le.mp (kernel_bound s t)).1
  calc
    _ = ∫ t : ℂ, -‖s‖ + B.indicator (fun _ : ℂ => v) t ∂μ := by
      rw [integral_add (integrable_const _) hi, integral_const,
        integral_indicator_const v hB]
      simp only [probReal_univ, smul_eq_mul]
      dsimp only [v, B]
      ring
    _ ≤ _ := integral_mono ((integrable_const _).add hi) (integrable_kernel μ s) hp

theorem linear_norm_coercive (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun z : ℂ => a * ‖z‖ + b) (cocompact ℂ) atTop := by
  have ht : Tendsto (fun z : ℂ => a * ‖z‖) (cocompact ℂ) atTop :=
    Filter.Tendsto.const_mul_atTop ha (tendsto_norm_cocompact_atTop (E := ℂ))
  exact tendsto_atTop_add_const_right (cocompact ℂ) b ht

theorem objective_coercive (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Tendsto (objective μ) (cocompact ℂ) atTop := by
  obtain ⟨n, hn⟩ := exists_ball_mass μ
  have hp : 0 < 2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1 := by linarith
  have ht := linear_norm_coercive (2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1)
    (-(μ.real (Metric.closedBall 0 (n : ℝ)) * (2 * (n : ℝ) + 1))) hp
  apply tendsto_atTop_mono (objective_lower μ (n : ℝ))
  simpa only [sub_eq_add_neg] using ht

theorem exists_unique_minimizer (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃! s, ∀ t, objective μ s ≤ objective μ t := by
  obtain ⟨s, hs⟩ := (continuous_objective μ).exists_forall_le (objective_coercive μ)
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact (objective_strict_convex μ).eq_of_isMinOn (fun x _ => ht x)
    (fun x _ => hs x) (Set.mem_univ t) (Set.mem_univ s)

noncomputable def center (μ : ProbabilityMeasure ℂ) : ℂ :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose

theorem center_minimizes (μ : ProbabilityMeasure ℂ) (s : ℂ) :
    objective (μ : Measure ℂ) (center μ) ≤ objective (μ : Measure ℂ) s :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.1 s

theorem center_unique (μ : ProbabilityMeasure ℂ) {z : ℂ}
    (hz : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t) :
    z = center μ := (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.2 z hz

noncomputable def universalKernel : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ) ℂ :=
  ⟨fun μ => (μ : Measure ℂ), measurable_subtype_coe⟩

theorem measurable_objective (s : ℂ) :
    Measurable (fun μ : ProbabilityMeasure ℂ => objective (μ : Measure ℂ) s) :=
  ((continuous_kernel s).stronglyMeasurable.integral_kernel
    (κ := universalKernel)).measurable

theorem denseSeq_inf_eq_min {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X] (f : X → ℝ) (hf : Continuous f) (x : X)
    (hx : ∀ y, f x ≤ f y) : (⨅ n, f (TopologicalSpace.denseSeq X n)) = f x := by
  have hb : BddBelow (Set.range (fun n => f (TopologicalSpace.denseSeq X n))) :=
    ⟨f x, by rintro _ ⟨n, rfl⟩; exact hx _⟩
  apply le_antisymm
  · exact (TopologicalSpace.denseRange_denseSeq X).induction_on
      (p := fun y => (⨅ n, f (TopologicalSpace.denseSeq X n)) ≤ f y) x
      (isClosed_le continuous_const hf) (fun n => ciInf_le hb n)
  · exact le_ciInf (fun n => hx _)

noncomputable def minValue (μ : ProbabilityMeasure ℂ) : ℝ :=
  ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq ℂ n)

theorem measurable_minValue : Measurable minValue :=
  Measurable.iInf fun _n => measurable_objective _

theorem minValue_eq (μ : ProbabilityMeasure ℂ) :
    minValue μ = objective (μ : Measure ℂ) (center μ) :=
  denseSeq_inf_eq_min _ (continuous_objective _) _ (center_minimizes μ)

theorem exists_min_on_closed (μ : ProbabilityMeasure ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCn : C.Nonempty) :
    ∃ z ∈ C, ∀ t ∈ C, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t := by
  obtain ⟨x, hx⟩ := hCn
  apply (continuous_objective (μ : Measure ℂ)).continuousOn.exists_isMinOn' hC hx
  apply Filter.Eventually.filter_mono inf_le_left
  exact (objective_coercive (μ : Measure ℂ)).eventually
    (eventually_ge_atTop (objective (μ : Measure ℂ) x))

theorem measurable_center : Measurable center := by
  classical
  apply measurable_of_isClosed
  intro C hC
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let mC (μ : ProbabilityMeasure ℂ) : ℝ :=
      ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq C n).val
    have hmC : Measurable mC := Measurable.iInf fun _n => measurable_objective _
    have he : center ⁻¹' C = {μ | mC μ = minValue μ} := by
      ext μ
      obtain ⟨z, hzC, hz⟩ := exists_min_on_closed μ hC hne
      have hm : mC μ = objective (μ : Measure ℂ) z :=
        denseSeq_inf_eq_min (fun t : C => objective (μ : Measure ℂ) t.val)
          ((continuous_objective _).comp continuous_subtype_val) ⟨z, hzC⟩
          (fun t => hz t.val t.property)
      rw [Set.mem_preimage, Set.mem_ofPred_eq, hm, minValue_eq]
      constructor
      · intro h
        exact le_antisymm (hz _ h) (center_minimizes μ z)
      · intro h
        have hzm : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t :=
          fun t => h.trans_le (center_minimizes μ t)
        rwa [center_unique μ hzm] at hzC
    rw [he]
    exact measurableSet_eq_fun hmC measurable_minValue
  · have he : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he]

theorem kernel_translate (s t v : ℂ) :
    kernel (s + v) (t + v) = kernel s t - kernel (-v) t := by
  have h₁ : s + v - (t + v) = s - t := by abel
  have h₂ : -(t + v) = -v - t := by abel
  simp only [kernel, h₁, h₂]
  ring

theorem objective_translate (μ : ProbabilityMeasure ℂ) (s v : ℂ) :
    objective (Measure.map (fun t => t + v) (μ : Measure ℂ)) (s + v) =
      objective (μ : Measure ℂ) s - objective (μ : Measure ℂ) (-v) := by
  have hm : AEMeasurable (fun t : ℂ => t + v) (μ : Measure ℂ) :=
    (continuous_id.add_const v).aemeasurable
  rw [objective, integral_map hm (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_translate]
  exact integral_sub (integrable_kernel _ _) (integrable_kernel _ _)

theorem center_translate (μ : ProbabilityMeasure ℂ) (v : ℂ) :
    center (μ.map (fun point => point + v)) = center μ + v := by
  apply Eq.symm
  apply center_unique
  intro t
  have he : t = (t - v) + v := by abel
  change objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) (center μ + v) ≤
    objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) t
  rw [objective_translate, he, objective_translate]
  exact sub_le_sub_right (center_minimizes μ (t - v)) _

theorem kernel_orthogonal (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s t : ℂ) :
    kernel (O s) (O t) = kernel s t := by
  simp only [kernel_formula, ← O.map_sub, O.norm_map]

theorem objective_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s : ℂ) :
    objective (Measure.map O (μ : Measure ℂ)) (O s) = objective (μ : Measure ℂ) s := by
  rw [objective, integral_map O.continuous.aemeasurable
    (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_orthogonal, objective]

theorem center_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) :
    center (μ.map O) = O (center μ) := by
  apply Eq.symm
  apply center_unique
  intro t
  obtain ⟨s, rfl⟩ := O.surjective t
  rw [ProbabilityMeasure.toMeasure_map, objective_orthogonal, objective_orthogonal]
  exact center_minimizes μ s

end EuclideanFiveColor.Location

namespace EuclideanFiveColor.CosetCenter
open ProbabilityTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

structure Embedding (G : Type*) [CommGroup G] [MeasurableSpace G] where
  hom : Multiplicative ℂ →* G
  measurableEmbedding : MeasurableEmbedding (fun z : ℂ => hom (Multiplicative.ofAdd z))

namespace Embedding

variable (e : Embedding G)

def j (z : ℂ) : G := e.hom (Multiplicative.ofAdd z)

@[simp] theorem j_zero : e.j 0 = 1 := e.hom.map_one
@[simp] theorem j_add (z w : ℂ) : e.j (z + w) = e.j z * e.j w := e.hom.map_mul _ _
@[simp] theorem j_neg (z : ℂ) : e.j (-z) = (e.j z)⁻¹ := e.hom.map_inv _
@[simp] theorem j_sub (z w : ℂ) : e.j (z - w) = e.j z / e.j w := e.hom.map_div _ _

theorem j_injective : Function.Injective e.j := e.measurableEmbedding.injective

theorem measurable_j : Measurable e.j := e.measurableEmbedding.measurable

def ordinary : Subgroup G := e.hom.range

theorem mem_ordinary_iff (x : G) : x ∈ e.ordinary ↔ ∃ z : ℂ, e.j z = x := Iff.rfl

theorem range_j : Set.range e.j = (e.ordinary : Set G) := rfl

theorem measurableSet_ordinary : MeasurableSet (e.ordinary : Set G) :=
  e.measurableEmbedding.measurableSet_range

noncomputable def coordinate : G → ℂ := Function.extend e.j id (fun _ => 0)

theorem measurable_coordinate : Measurable e.coordinate :=
  e.measurableEmbedding.measurable_extend measurable_id measurable_const

@[simp] theorem coordinate_j (z : ℂ) : e.coordinate (e.j z) = z :=
  e.j_injective.extend_apply id (fun _ => 0) z

theorem j_coordinate {x : G} (hx : x ∈ e.ordinary) : e.j (e.coordinate x) = x := by
  obtain ⟨z, rfl⟩ := (e.mem_ordinary_iff x).mp hx
  simp

variable [MeasurableMul₂ G] [MeasurableInv G]

def coset (z : G) : Set G := {d | d / z ∈ e.ordinary}

theorem measurableSet_coset (z : G) : MeasurableSet (e.coset z) :=
  e.measurableSet_ordinary.preimage (measurable_id.div_const z)

noncomputable def frequencyMeasure (μ : Measure G) (z : G) : Measure ℂ :=
  (μ.restrict (e.coset z)).map (fun d => e.coordinate (d / z))

theorem frequencyMeasure_apply (μ : Measure G) (z : G) {s : Set ℂ}
    (hs : MeasurableSet s) :
    e.frequencyMeasure μ z s = μ {d | d / z ∈ e.ordinary ∧ e.coordinate (d / z) ∈ s} := by
  rw [frequencyMeasure, Measure.map_apply
    (show Measurable (fun d : G => e.coordinate (d / z)) from
      e.measurable_coordinate.comp (measurable_id.div_const z)) hs,
    Measure.restrict_apply (show MeasurableSet ((fun d : G => e.coordinate (d / z)) ⁻¹' s) from
      (e.measurable_coordinate.comp (measurable_id.div_const z)) hs)]
  congr 1
  ext d
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, coset]
  exact and_comm

@[simp] theorem frequencyMeasure_univ (μ : Measure G) (z : G) :
    e.frequencyMeasure μ z Set.univ = μ (e.coset z) := by
  rw [e.frequencyMeasure_apply μ z MeasurableSet.univ]
  congr 1
  ext d
  simp [coset]

noncomputable def parameterKernel : Kernel (ProbabilityMeasure G × G) G :=
  ⟨fun p => (p.1 : Measure G), measurable_subtype_coe.comp measurable_fst⟩

instance parameterKernel_markov : IsMarkovKernel (parameterKernel (G := G)) :=
  ⟨fun p => by change IsProbabilityMeasure (p.1 : Measure G); infer_instance⟩

theorem measurable_frequencyMeasure :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyMeasure (p.1 : Measure G) p.2) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm : Measurable (fun p : (ProbabilityMeasure G × G) × G =>
      if p.2 / p.1.2 ∈ e.ordinary ∧ e.coordinate (p.2 / p.1.2) ∈ s
      then (1 : ℝ≥0∞) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (e.measurableSet_ordinary.preimage
      (measurable_snd.div (measurable_snd.comp measurable_fst))).inter
      (hs.preimage (e.measurable_coordinate.comp
        (measurable_snd.div (measurable_snd.comp measurable_fst))))
  have h := hm.lintegral_kernel_prod_right' (κ := parameterKernel (G := G))
  convert h using 1
  ext p
  rw [e.frequencyMeasure_apply _ _ hs]
  have hset : MeasurableSet {d : G | d / p.2 ∈ e.ordinary ∧
      e.coordinate (d / p.2) ∈ s} :=
    (e.measurableSet_ordinary.preimage (measurable_id.div_const p.2)).inter
      (hs.preimage (e.measurable_coordinate.comp (measurable_id.div_const p.2)))
  rw [show parameterKernel p = (p.1 : Measure G) from rfl]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    (lintegral_indicator_one (μ := (p.1 : Measure G)) hset).symm

theorem measurable_mass : Measurable (fun p : ProbabilityMeasure G × G =>
    (p.1 : Measure G) (e.coset p.2)) := by
  have h : Measurable (fun p : ProbabilityMeasure G × G =>
      e.frequencyMeasure (p.1 : Measure G) p.2 Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp e.measurable_frequencyMeasure
  simp only [frequencyMeasure_univ] at h
  exact h

noncomputable def frequencyLaw (μ : ProbabilityMeasure G) (z : G) : ProbabilityMeasure ℂ :=
  if h : (μ : Measure G) (e.coset z) = 0 then ⟨Measure.dirac 0, inferInstance⟩
  else
    letI : IsProbabilityMeasure ((μ : Measure G)[|e.coset z]) :=
      cond_isProbabilityMeasure h
    ⟨((μ : Measure G)[|e.coset z]).map (fun d => e.coordinate (d / z)),
      inferInstance⟩

theorem frequencyLaw_measure (μ : ProbabilityMeasure G) (z : G) :
    (e.frequencyLaw μ z : Measure ℂ) =
      if (μ : Measure G) (e.coset z) = 0 then Measure.dirac 0 else
      ((μ : Measure G) (e.coset z))⁻¹ • e.frequencyMeasure μ z := by
  split_ifs with h
  · simp [frequencyLaw, h]
  · simp [frequencyLaw, h, ProbabilityTheory.cond, frequencyMeasure]
    exact Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹
      (e.measurable_coordinate.comp (measurable_id.div_const z)).aemeasurable

theorem measurable_frequencyLaw :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyLaw p.1 p.2) := by
  have hm : Measurable (fun p : ProbabilityMeasure G × G =>
      (e.frequencyLaw p.1 p.2 : Measure ℂ)) := by
    simp_rw [frequencyLaw_measure]
    apply Measurable.ite (e.measurable_mass (measurableSet_singleton 0)) measurable_const
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact e.measurable_mass.inv.mul ((Measure.measurable_coe hs).comp e.measurable_frequencyMeasure)
  exact hm.subtype_mk

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coset_mul_j (z : G) (v : ℂ) : e.coset (z * e.j v) = e.coset z := by
  ext d
  have hj : e.j v ∈ e.ordinary := ⟨_, rfl⟩
  constructor
  · intro h
    change d / z ∈ e.ordinary
    convert e.ordinary.mul_mem h hj using 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  · intro h
    change d / (z * e.j v) ∈ e.ordinary
    convert e.ordinary.div_mem h hj using 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coordinate_div_j {d : G} (hd : d ∈ e.ordinary) (v : ℂ) :
    e.coordinate (d / e.j v) = e.coordinate d - v := by
  rw [← e.j_coordinate hd, ← e.j_sub, e.coordinate_j, e.coordinate_j]

theorem frequencyMeasure_shift (μ : Measure G) (z : G) (v : ℂ) :
    e.frequencyMeasure μ (z * e.j v) =
      (e.frequencyMeasure μ z).map (fun t => t + -v) := by
  rw [frequencyMeasure, frequencyMeasure, e.coset_mul_j,
    Measure.map_map (show Measurable (fun t : ℂ => t + -v) from
      measurable_id.add_const (-v))
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (d / (z * e.j v)) = e.coordinate (d / z) + -v
  rw [div_mul_eq_div_div, e.coordinate_div_j hd, sub_eq_add_neg]

theorem frequencyLaw_shift (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw μ (z * e.j v) =
      (e.frequencyLaw μ z).map (fun point => point + -v) := by
  apply Subtype.ext
  change (e.frequencyLaw μ (z * e.j v) : Measure ℂ) =
    Measure.map (fun t => t + -v) (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, e.coset_mul_j]
  simp only [ite_eq_right h]
  rw [Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹
    (f := fun point : ℂ => point + -v) (continuous_id.add_const (-v)).aemeasurable,
    ← e.frequencyMeasure_shift]

noncomputable def center (μ : ProbabilityMeasure G) (z : G) : G :=
  z * e.j (Location.center (e.frequencyLaw μ z))

theorem measurable_center :
    Measurable (fun p : ProbabilityMeasure G × G => e.center p.1 p.2) :=
  measurable_snd.mul (e.measurable_j.comp
    (Location.measurable_center.comp e.measurable_frequencyLaw))

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem center_mem_coset (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.coset z := by
  change z * e.j _ / z ∈ e.ordinary
  rw [mul_div_cancel_left]
  exact ⟨_, rfl⟩

theorem center_mul_j (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ (z * e.j v) = e.center μ z := by
  rw [center, e.frequencyLaw_shift μ z v h, Location.center_translate, e.j_add,
    e.j_neg, center]
  simp [mul_assoc, mul_comm]

theorem center_eq_of_mem_coset (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) (hz' : z' ∈ e.coset z) :
    e.center μ z' = e.center μ z := by
  obtain ⟨v, hv⟩ := (e.mem_ordinary_iff (z' / z)).mp hz'
  have he : z' = z * e.j v := by rw [hv]; simp [div_eq_mul_inv]
  rw [he]
  exact e.center_mul_j μ z v hz

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem quotient_center (μ : ProbabilityMeasure G) (z : G) :
    (QuotientGroup.mk (e.center μ z) : G ⧸ e.ordinary) = QuotientGroup.mk z :=
  QuotientGroup.eq_iff_div_mem.mpr (e.center_mem_coset μ z)

theorem center_eq_iff (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ z' = e.center μ z ↔ z' ∈ e.coset z := by
  constructor
  · intro h
    change z' / z ∈ e.ordinary
    apply QuotientGroup.eq_iff_div_mem.mp
    rw [← e.quotient_center μ z', ← e.quotient_center μ z, h]
  · exact e.center_eq_of_mem_coset μ hz

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem center_mem_ordinary_iff (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.ordinary ↔ z ∈ e.ordinary := by
  rw [← QuotientGroup.eq_one_iff, e.quotient_center, QuotientGroup.eq_one_iff]

theorem preimage_center_singleton (μ : ProbabilityMeasure G) {z : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    (e.center μ) ⁻¹' {e.center μ z} = e.coset z := by
  ext z'
  exact e.center_eq_iff μ hz

theorem measurable_center_fixed (μ : ProbabilityMeasure G) : Measurable (e.center μ) :=
  e.measurable_center.comp (measurable_const.prodMk measurable_id)

variable (T : G ≃* G) (O : ℂ ≃ₗᵢ[ℝ] ℂ)
  (hT : Measurable T) (he : ∀ t : ℂ, T (e.j t) = e.j (O t))

include he

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem equiv_mem_ordinary_iff (d : G) : T d ∈ e.ordinary ↔ d ∈ e.ordinary := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd (O.symm (Multiplicative.toAdd t)), ?_⟩
    change e.j (O.symm _) = d
    apply T.injective
    rw [he, O.apply_symm_apply]
    exact ht
  · rintro ⟨t, rfl⟩
    exact (e.mem_ordinary_iff _).mpr ⟨O (Multiplicative.toAdd t), (he _).symm⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem preimage_coset_equiv (z : G) : T ⁻¹' e.coset (T z) = e.coset z := by
  ext d
  change T d / T z ∈ e.ordinary ↔ d / z ∈ e.ordinary
  rw [← T.map_div]
  exact e.equiv_mem_ordinary_iff T O he _

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coordinate_equiv {d : G} (hd : d ∈ e.ordinary) :
    e.coordinate (T d) = O (e.coordinate d) := by
  obtain ⟨t, rfl⟩ := (e.mem_ordinary_iff d).mp hd
  rw [he, e.coordinate_j, e.coordinate_j]

include hT in
theorem frequencyMeasure_equiv (μ : Measure G) (z : G) :
    e.frequencyMeasure (μ.map T) (T z) = (e.frequencyMeasure μ z).map O := by
  rw [frequencyMeasure, Measure.restrict_map hT (e.measurableSet_coset _),
    e.preimage_coset_equiv T O he,
    Measure.map_map (show Measurable (fun d : G => e.coordinate (d / T z)) from
      e.measurable_coordinate.comp (measurable_id.div_const (T z))) hT,
    frequencyMeasure,
    Measure.map_map O.continuous.measurable
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (T d / T z) = O (e.coordinate (d / z))
  rw [← T.map_div]
  exact e.coordinate_equiv T O he hd

include hT in
theorem frequencyLaw_equiv (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw (μ.map T) (T z) =
      (e.frequencyLaw μ z).map O := by
  apply Subtype.ext
  change (e.frequencyLaw (μ.map T) (T z) : Measure ℂ) =
    Measure.map O (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hT (e.measurableSet_coset _), e.preimage_coset_equiv T O he,
    ]
  simp only [ite_eq_right hz]
  rw [Measure.map_smul _ O.continuous.aemeasurable,
    e.frequencyMeasure_equiv T O hT he]

include hT in
theorem center_equivariant (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center (μ.map T) (T z) = T (e.center μ z) := by
  rw [center, e.frequencyLaw_equiv T O hT he μ z hz, Location.center_orthogonal,
    center, T.map_mul, he]

end Embedding
end EuclideanFiveColor.CosetCenter

end

end OAI
