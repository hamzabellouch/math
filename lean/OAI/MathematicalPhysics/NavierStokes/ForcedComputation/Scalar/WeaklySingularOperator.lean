import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.WeaklySingularContinuity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! A weakly singular Volterra integral as a bounded linear operator on continuous paths. -/

noncomputable section
namespace ForcedComputation.WeaklySingular

open Real MeasureTheory Set Filter
open scoped Topology Interval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem volterra_integrable (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (hK : ContinuousOn K (Ioi 0)) (hu : Continuous u)
    (C B : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (hub : ∀ s, ‖u s‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => K (t - s) (u s)) volume 0 t := by
  have hm : AEStronglyMeasurable (fun s => K (t - s) (u s)) (volume.restrict (Ioc 0 t)) := by
    have hc : ContinuousOn (fun s => K (t - s) (u s)) (Ioo 0 t) := by
      intro s hs
      have hk := (hK.continuousAt (Ioi_mem_nhds (sub_pos.mpr hs.2))).comp
        (continuousAt_const.sub continuousAt_id)
      exact (hk.clm_apply hu.continuousAt).continuousWithinAt
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hc.aestronglyMeasurable measurableSet_Ioo
  apply intervalIntegrable_of_inverseSqrt_bound E ht _ (C * B) hm
  intro s hs
  have hp : 0 ≤ t - s := sub_nonneg.mpr hs.2
  calc
    _ ≤ ‖K (t - s)‖ * ‖u s‖ := (K (t - s)).le_opNorm (u s)
    _ ≤ (C * inverseSqrt (t - s)) * B :=
      mul_le_mul (hbound _ hp) (hub s) (norm_nonneg _)
        (mul_nonneg hC (inverseSqrt_nonneg _))
    _ = _ := by ring

/-- A fixed normed-space structure for continuous paths on the closed time interval. -/
def Path (T : ℝ) := C(Icc (0 : ℝ) T, E)

instance (T : ℝ) : NormedAddCommGroup (Path E T) :=
  inferInstanceAs (NormedAddCommGroup C(Icc (0 : ℝ) T, E))
instance (T : ℝ) : NormedSpace ℝ (Path E T) :=
  inferInstanceAs (NormedSpace ℝ C(Icc (0 : ℝ) T, E))
instance (T : ℝ) [CompleteSpace E] : CompleteSpace (Path E T) :=
  inferInstanceAs (CompleteSpace C(Icc (0 : ℝ) T, E))

def pathEquiv (T : ℝ) : Path E T ≃ₗᵢ[ℝ] C(Icc (0 : ℝ) T, E) :=
  LinearIsometryEquiv.refl ℝ _

instance (T : ℝ) : CoeFun (Path E T) (fun _ => Icc (0 : ℝ) T → E) :=
  ⟨fun u => pathEquiv E T u⟩

/-- Constant continuation beyond the endpoints gives a global bounded continuous source. -/
def extendPath {T : ℝ} (hT : 0 ≤ T) (u : Path E T) (s : ℝ) : E :=
  u (projIcc 0 T hT s)

theorem continuous_extendPath {T : ℝ} (hT : 0 ≤ T) (u : Path E T) :
    Continuous (extendPath E hT u) :=
  (pathEquiv E T u).continuous.comp continuous_projIcc

theorem norm_extendPath_le {T : ℝ} (hT : 0 ≤ T) (u : Path E T) (s : ℝ) :
    ‖extendPath E hT u s‖ ≤ ‖u‖ :=
  ((pathEquiv E T u).norm_coe_le_norm _).trans_eq ((pathEquiv E T).norm_map u)

@[simp] theorem extendPath_coe {T : ℝ} (hT : 0 ≤ T) (u : Path E T) (s : Icc (0 : ℝ) T) :
    extendPath E hT u s = u s := by
  simp only [extendPath, projIcc_val]

private def integralPath {T : ℝ} (hT : 0 ≤ T) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (u : Path E T) : Path E T :=
  (pathEquiv E T).symm
    { toFun := fun t => volterra E K (extendPath E hT u) t
      continuous_toFun :=
        (continuousOn_volterra E K (extendPath E hT u) hK
          (continuous_extendPath E hT u) C ‖u‖ hC hbound
          (norm_extendPath_le E hT u)).comp_continuous continuous_subtype_val
            (fun t => t.property.1) }

private theorem norm_integralPath_le {T : ℝ} (hT : 0 ≤ T) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (u : Path E T) :
    ‖integralPath E hT K hK C hC hbound u‖ ≤ (2 * C * Real.sqrt T) * ‖u‖ := by
  rw [← (pathEquiv E T).norm_map (integralPath E hT K hK C hC hbound u)]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖volterra E K (extendPath E hT u) t.val‖ ≤ _
  calc
    _ ≤ 2 * C * ‖u‖ * Real.sqrt t.val :=
      norm_volterra_le E t.property.1 K (extendPath E hT u) C ‖u‖ hC
        (fun r hr => hbound r hr.1) (fun s _ => norm_extendPath_le E hT u s)
    _ ≤ 2 * C * ‖u‖ * Real.sqrt T :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt t.property.2) (by positivity)
    _ = _ := by ring

/-- The actual Volterra operator on continuous paths; its norm is bounded by `2 C sqrt T`. -/
def integralOperator {T : ℝ} (hT : 0 ≤ T) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r) :
    Path E T →L[ℝ] Path E T :=
  LinearMap.mkContinuous
    { toFun := integralPath E hT K hK C hC hbound
      map_add' := by
        intro u v
        apply (pathEquiv E T).injective
        rw [map_add]
        apply ContinuousMap.ext
        intro t
        change (∫ s in 0..t.val, K (t.val - s) (extendPath E hT (u + v) s)) =
          (∫ s in 0..t.val, K (t.val - s) (extendPath E hT u s)) +
            ∫ s in 0..t.val, K (t.val - s) (extendPath E hT v s)
        have he (s : ℝ) : extendPath E hT (u + v) s =
            extendPath E hT u s + extendPath E hT v s := rfl
        simp_rw [he, map_add]
        exact intervalIntegral.integral_add
          (volterra_integrable E K (extendPath E hT u) hK (continuous_extendPath E hT u)
            C ‖u‖ hC hbound (norm_extendPath_le E hT u) t.property.1)
          (volterra_integrable E K (extendPath E hT v) hK (continuous_extendPath E hT v)
            C ‖v‖ hC hbound (norm_extendPath_le E hT v) t.property.1)
      map_smul' := by
        intro c u
        apply (pathEquiv E T).injective
        rw [map_smul]
        apply ContinuousMap.ext
        intro t
        change (∫ s in 0..t.val, K (t.val - s) (extendPath E hT (c • u) s)) =
          c • ∫ s in 0..t.val, K (t.val - s) (extendPath E hT u s)
        have he (s : ℝ) : extendPath E hT (c • u) s = c • extendPath E hT u s := rfl
        simp_rw [he, map_smul]
        exact intervalIntegral.integral_smul c _ }
    (2 * C * Real.sqrt T) (norm_integralPath_le E hT K hK C hC hbound)

@[simp] theorem integralOperator_apply {T : ℝ} (hT : 0 ≤ T) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (u : Path E T) (t : Icc (0 : ℝ) T) :
    integralOperator E hT K hK C hC hbound u t =
      ∫ s in 0..t.val, K (t.val - s) (extendPath E hT u s) := rfl

theorem norm_integralOperator_le {T : ℝ} (hT : 0 ≤ T) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r) :
    ‖integralOperator E hT K hK C hC hbound‖ ≤ 2 * C * Real.sqrt T :=
  (integralOperator E hT K hK C hC hbound).opNorm_le_bound (by positivity)
    (norm_integralPath_le E hT K hK C hC hbound)

end ForcedComputation.WeaklySingular

end

end OAI
