import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeContinuation
import OAI.Probability.MemoryPrecision.JointL1

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section RadialCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialShrink (c : ℝ) (v : E) : E :=
  (Real.sqrt (‖v‖^2 + c^2))⁻¹ • v

def radialExpand (c : ℝ) (u : E) : E :=
  (c / Real.sqrt (1 - ⟪u,u⟫)) • u

lemma radialShrink_mem_ball {c : ℝ} (hc : 0 < c) (v : E) :
    radialShrink c v ∈ Metric.ball 0 1 := by
  have hp : 0 < ‖v‖^2 + c^2 := by positivity
  have hs : 0 < Real.sqrt (‖v‖^2 + c^2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  rw [Metric.mem_ball, dist_zero_right, radialShrink, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hlt : ‖v‖ < Real.sqrt (‖v‖^2 + c^2) := by nlinarith [sq_pos_of_pos hc]
  simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hs).mpr hlt

lemma radialExpand_shrink {c : ℝ} (hc : 0 < c) (v : E) :
    radialExpand c (radialShrink c v) = v := by
  let t := Real.sqrt (‖v‖^2+c^2)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t^2 = ‖v‖^2+c^2 := Real.sq_sqrt (by positivity)
  have he : 1 - ⟪radialShrink c v,radialShrink c v⟫ = (c/t)^2 := by
    simp only [radialShrink, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq]
    change 1 - t⁻¹ * (t⁻¹ * ‖v‖^2) = (c/t)^2
    field_simp
    nlinarith [ht2]
  rw [radialExpand, he, Real.sqrt_sq (le_of_lt (div_pos hc ht)), radialShrink,
    smul_smul]
  change (c / (c/t) * t⁻¹) • v = v
  have he' : c / (c/t) * t⁻¹ = 1 := by field_simp
  rw [he', one_smul]

lemma radialExpand_differentiableOn (c : ℝ) :
    DifferentiableOn ℝ (radialExpand (E := E) c) (Metric.ball 0 1) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa using hu
  have hpos : 0 < 1 - ⟪u,u⟫ := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg u]
  apply DifferentiableAt.differentiableWithinAt
  unfold radialExpand
  apply DifferentiableAt.smul
  · simp only [div_eq_mul_inv]
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.inv
    · apply DifferentiableAt.sqrt
      · exact (differentiableAt_const 1).sub
          (DifferentiableAt.inner ℝ differentiableAt_id differentiableAt_id)
      · exact ne_of_gt hpos
    · exact ne_of_gt (Real.sqrt_pos.2 hpos)
  · exact differentiableAt_id

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma radialShrink_preimage_null {c : ℝ} (hc : 0 < c) {s : Set E}
    (hs : volume s = 0) : volume (radialShrink c ⁻¹' s) = 0 := by
  have hn : volume (s ∩ Metric.ball (0:E) 1) = 0 :=
    measure_mono_null Set.inter_subset_left hs
  have hi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((radialExpand_differentiableOn (E:=E) c).mono Set.inter_subset_right) hn
  apply measure_mono_null _ hi
  intro v hv
  refine ⟨radialShrink c v, ⟨hv, radialShrink_mem_ball hc v⟩, ?_⟩
  exact radialExpand_shrink hc v
end RadialCoordinates

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orthogonal_normalized_preimage_null (K : Submodule ℝ E) [Nontrivial Kᗮ]
    {s : Set K} (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} = 0 := by
  let e : (Kᗮ × K) ≃ₗ[ℝ] E :=
    (LinearEquiv.prodComm ℝ Kᗮ K).trans (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal)
  let t : Set (Kᗮ × K) := {x | radialShrink ‖x.1‖ x.2 ∈ s}
  have ht : MeasurableSet t := by
    apply hs.preimage
    dsimp [radialShrink]
    fun_prop
  have ht0 : ((volume : Measure Kᗮ).prod (volume : Measure K)) t = 0 := by
    rw [Measure.prod_apply ht]
    rw [← lintegral_zero (μ := (volume : Measure Kᗮ))]
    apply lintegral_congr_ae
    have hk : ∀ᵐ k : Kᗮ ∂volume, k ≠ 0 := by
      simpa only [Ne, ← Set.mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0:Kᗮ)))
    filter_upwards [hk] with k hk
    exact radialShrink_preimage_null (norm_pos_iff.mpr hk) hs0
  have hn : MeasurableSet {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} := by
    apply hs.preimage
    exact measurable_id.norm.inv.smul K.orthogonalProjectionOnto.continuous.measurable
  have hnt : e ⁻¹' {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} = t := by
    ext x
    have hp : K.orthogonalProjectionOnto (e x) = x.2 := by
      change K.orthogonalProjectionOnto ((x.2:E)+(x.1:E)) = x.2
      rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.1.property, add_zero]
    have hnorm : ‖e x‖ = Real.sqrt (‖x.2‖^2 + ‖x.1‖^2) := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x.2:E) (x.1:E)
        (Submodule.inner_right_of_mem_orthogonal x.2.property x.1.property)
      have he : ‖e x‖^2 = ‖x.2‖^2 + ‖x.1‖^2 := by
        change ‖(x.2:E)+(x.1:E)‖^2 = _
        simpa only [pow_two, Submodule.norm_coe] using h
      rw [← he, Real.sqrt_sq (norm_nonneg _)]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hp, hnorm, t, radialShrink]
  let : ((((volume : Measure Kᗮ).prod (volume : Measure K)).map e)).IsAddHaarMeasure :=
    Measure.MapLinearEquiv.isAddHaarMeasure _ e
  have heac : (volume : Measure E) ≪
      (((volume : Measure Kᗮ).prod (volume : Measure K)).map e) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply heac
  rw [Measure.map_apply (f := e) e.toContinuousLinearEquiv.continuous.measurable hn, hnt, ht0]

lemma sphere_projection_ac (K : Submodule ℝ E) [Nontrivial E] [Nontrivial Kᗮ] :
    ((sphereLaw (E:=E)).map (fun x => K.orthogonalProjectionOnto x.val)) ≪
      (volume : Measure K) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hm : Measurable (fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) :=
    K.orthogonalProjectionOnto.continuous.measurable.comp measurable_subtype_coe
  rw [Measure.map_apply hm hs, sphereLaw_apply (hm hs)]
  have hn := orthogonal_normalized_preimage_null K hs hs0
  have hcone : volume (Set.Ioo (0:ℝ) 1 •
      (Subtype.val '' ((fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) ⁻¹' s))) = 0 := by
    apply measure_mono_null _ hn
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    change ‖r • x.val‖⁻¹ • K.orthogonalProjectionOnto (r • x.val) ∈ s
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
      mem_sphere_zero_iff_norm.mp x.property, mul_one, map_smul, smul_smul,
      inv_mul_cancel₀ hr.1.ne', one_smul]
    exact hx
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet]
  rw [measure_mono_null Set.inter_subset_left hcone, mul_zero]

lemma sphere_rows_ac [Nontrivial E] {m : ℕ} (A : Fin m → E)
    (hA : LinearIndependent ℝ A) (hm : m < Module.finrank ℝ E) :
    ((sphereLaw (E:=E)).map
      (fun x : Metric.sphere (0:E) 1 => fun j => ⟪x.val,A j⟫)) ≪
      (volume : Measure (Fin m → ℝ)) := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range A)
  have hd : Module.finrank ℝ K = m := by
    simpa only [K, Fintype.card_fin] using finrank_span_eq_card hA
  have hK : K ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hd
    omega
  have : Nontrivial Kᗮ := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h => hK (Submodule.orthogonal_eq_bot_iff.mp h))
  let L : K →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun j => (innerSL ℝ (A j)).toLinearMap.comp K.subtype)
  have hLi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro x hx
    have hle : K ≤ (innerSL ℝ (x:E)).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change ⟪(x:E),A j⟫ = 0
      have hj := congrFun hx j
      change ⟪A j,(x:E)⟫ = 0 at hj
      rwa [real_inner_comm]
    have hz : ⟪(x:E),(x:E)⟫ = 0 := hle x.property
    exact Subtype.ext (inner_self_eq_zero.mp hz)
  have hdim : Module.finrank ℝ K = Module.finrank ℝ (Fin m → ℝ) := by
    simpa using hd
  let e : K ≃ₗ[ℝ] (Fin m → ℝ) :=
    LinearEquiv.ofBijective L ⟨hLi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLi⟩
  have he : (fun x : Metric.sphere (0:E) 1 => fun j => ⟪x.val,A j⟫) =
      e ∘ (fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) := by
    funext x j
    change ⟪x.val,A j⟫ = ⟪A j,(K.orthogonalProjectionOnto x.val:E)⟫
    have hp := K.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨A j, Submodule.subset_span ⟨j,rfl⟩⟩ x.val
    change ⟪A j,(K.orthogonalProjectionOnto x.val:E)⟫ = ⟪A j,x.val⟫ at hp
    rw [hp, real_inner_comm]
  rw [he, ← Measure.map_map (f := fun x : Metric.sphere (0:E) 1 =>
    K.orthogonalProjectionOnto x.val) (g := e)
    e.toContinuousLinearEquiv.continuous.measurable (by fun_prop)]
  apply ((sphere_projection_ac K).map
    (show Measurable e from e.toContinuousLinearEquiv.continuous.measurable)).trans
  let : ((volume : Measure K).map e).IsAddHaarMeasure :=
    Measure.MapLinearEquiv.isAddHaarMeasure _ e
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _
end Projection

theorem spherical_projection_ac {d m : ℕ} (hd : 2 ≤ d) (hm : m < d)
    (A : Fin m → Space d) (hA : LinearIndependent ℝ A)
    (μ : Measure (Space d)) (hμ : μ ≪ UniformSphere d) :
    μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ)) := by
  have : NeZero d := ⟨by omega⟩
  apply (hμ.map (by fun_prop)).trans
  have h := sphere_rows_ac A hA (by simpa using hm)
  simpa only [UniformSphere, Kernel.UniformSphere, sphereLaw, Measure.map_map (by fun_prop :
    Measurable (fun s : Space d => fun j => ⟪s,A j⟫)) measurable_subtype_coe,
    Function.comp_def] using h
end MemoryPrecision


end

end OAI
