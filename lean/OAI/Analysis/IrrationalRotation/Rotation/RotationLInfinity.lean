import OAI.Analysis.IrrationalRotation.Model.RotationLInfinity
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem ae_all_action (θ : ℝ) {p : Circle → Prop} (hp : ∀ᵐ x ∂circleMeasure, p x) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, p (action θ k x) :=
  ae_all_iff.mpr fun k => (action_measurePreserving θ k).quasiMeasurePreserving.ae hp

theorem lInfinityOrbitWeight_ae (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, lInfinityOrbitWeight θ a x k = a (action θ k x) := by
  change ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
    LInfinityRepresentative.value a (action θ k x) = a (action θ k x)
  exact ae_all_action θ (p := fun x => LInfinityRepresentative.value a x = a x)
    (LInfinityRepresentative.value_ae a)

theorem lInfinityRepresentation_coordinate_ae (θ : ℝ) (a : Lp ℂ ∞ circleMeasure)
    (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      lInfinityRepresentation θ a ξ x k = a (action θ k x) * ξ x k := by
  have h := WeightedShift.fieldDiagonal_coordinate_ae
    (lInfinityOrbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a)
      (fun k => LInfinityRepresentative.norm_value_le a _))
    (fun k => ((LInfinityRepresentative.stronglyMeasurable_value a).comp_measurable
      (continuous_id.add continuous_const).measurable).aestronglyMeasurable) ξ
  filter_upwards [h, lInfinityOrbitWeight_ae θ a] with x hx ha k
  exact (hx k).trans (congrArg (fun z : ℂ => z * ξ x k) (ha k))

theorem norm_lInfinityRepresentation_le (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    ‖lInfinityRepresentation θ a‖ ≤ ‖a‖ :=
  WeightedShift.norm_fieldDiagonal_le _ _ _ _ _

theorem lInfinityRepresentation_continuous (θ : ℝ) (a : C(Circle, ℂ)) :
    lInfinityRepresentation θ (ContinuousMap.toLp ∞ circleMeasure ℂ a) =
      representation θ a := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [lInfinityRepresentation_coordinate_ae θ
    (ContinuousMap.toLp ∞ circleMeasure ℂ a) ξ,
    representation_ae θ a ξ,
    ae_all_action θ (ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) circleMeasure a)] with x h1 h2 ha
  apply lp.ext
  funext k
  rw [h2]
  change lInfinityRepresentation θ (ContinuousMap.toLp ∞ circleMeasure ℂ a) ξ x k =
    a (action θ k x) * ξ x k
  rw [h1, ha]

theorem lInfinityRepresentation_add (θ : ℝ) (a b : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ (a + b) =
      lInfinityRepresentation θ a + lInfinityRepresentation θ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [lInfinityRepresentation_coordinate_ae θ (a + b) ξ,
    lInfinityRepresentation_coordinate_ae θ a ξ,
    lInfinityRepresentation_coordinate_ae θ b ξ,
    ae_all_action θ (Lp.coeFn_add a b),
    Lp.coeFn_add (lInfinityRepresentation θ a ξ) (lInfinityRepresentation θ b ξ)]
    with x hab ha hb hc hout
  apply lp.ext
  funext k
  change lInfinityRepresentation θ (a + b) ξ x k =
    (lInfinityRepresentation θ a ξ + lInfinityRepresentation θ b ξ) x k
  rw [hab, hout]
  change (a + b) (action θ k x) * ξ x k =
    lInfinityRepresentation θ a ξ x k + lInfinityRepresentation θ b ξ x k
  rw [hc, ha, hb]
  exact add_mul _ _ _

theorem lInfinityRepresentation_smul (θ : ℝ) (c : ℂ) (a : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ (c • a) = c • lInfinityRepresentation θ a := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [lInfinityRepresentation_coordinate_ae θ (c • a) ξ,
    lInfinityRepresentation_coordinate_ae θ a ξ,
    ae_all_action θ (Lp.coeFn_smul c a),
    Lp.coeFn_smul c (lInfinityRepresentation θ a ξ)] with x hca ha hc hout
  apply lp.ext
  funext k
  change lInfinityRepresentation θ (c • a) ξ x k = (c • lInfinityRepresentation θ a ξ) x k
  rw [hca, hout]
  change (c • a) (action θ k x) * ξ x k = c * lInfinityRepresentation θ a ξ x k
  rw [hc, ha]
  exact mul_assoc _ _ _

def lInfinityRepresentationCLM (θ : ℝ) :
    Lp ℂ ∞ circleMeasure →L[ℂ] (Hilbert →L[ℂ] Hilbert) :=
  LinearMap.mkContinuous
    { toFun := lInfinityRepresentation θ
      map_add' := lInfinityRepresentation_add θ
      map_smul' := lInfinityRepresentation_smul θ }
    1 (fun a => by simpa using norm_lInfinityRepresentation_le θ a)

theorem lInfinityProduct_ae (a b : Lp ℂ ∞ circleMeasure) :
    lInfinityProduct a b =ᵐ[circleMeasure] fun x => a x * b x :=
  (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder a b

theorem lInfinityRepresentation_mul (θ : ℝ) (a b : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ (lInfinityProduct a b) =
      lInfinityRepresentation θ a * lInfinityRepresentation θ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [lInfinityRepresentation_coordinate_ae θ (lInfinityProduct a b) ξ,
    lInfinityRepresentation_coordinate_ae θ a (lInfinityRepresentation θ b ξ),
    lInfinityRepresentation_coordinate_ae θ b ξ,
    ae_all_action θ (p := fun x => lInfinityProduct a b x = a x * b x)
      (lInfinityProduct_ae a b)] with x hab ha hb hc
  apply lp.ext
  funext k
  change lInfinityRepresentation θ (lInfinityProduct a b) ξ x k =
    lInfinityRepresentation θ a (lInfinityRepresentation θ b ξ) x k
  rw [hab, ha, hb, hc]
  exact mul_assoc _ _ _

theorem lInfinityRepresentation_star (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ (star a) = star (lInfinityRepresentation θ a) := by
  unfold lInfinityRepresentation
  apply WeightedShift.fieldDiagonal_star_of_eq
  filter_upwards [lInfinityOrbitWeight_ae θ (star a), lInfinityOrbitWeight_ae θ a,
    ae_all_action θ (p := fun x => (star a) x = star (a x)) (Lp.coeFn_star a)]
    with x hs ha hstar
  apply lp.ext
  funext k
  change lInfinityOrbitWeight θ (star a) x k = star (lInfinityOrbitWeight θ a x k)
  rw [hs, ha, hstar]

theorem lInfinityRepresentation_one (θ : ℝ) :
    lInfinityRepresentation θ (Lp.const ∞ circleMeasure (1 : ℂ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [lInfinityRepresentation_coordinate_ae θ (Lp.const ∞ circleMeasure (1 : ℂ)) ξ,
    ae_all_action θ (p := fun x => Lp.const ∞ circleMeasure (1 : ℂ) x = 1)
      (Lp.coeFn_const ∞ circleMeasure (1 : ℂ))] with x hx hone
  apply lp.ext
  funext k
  change lInfinityRepresentation θ (Lp.const ∞ circleMeasure (1 : ℂ)) ξ x k = ξ x k
  rw [hx, hone, one_mul]

theorem lInfinityRepresentation_vacuum_eq_zero_iff (θ : ℝ)
    (a : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ a vacuum = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hout : lInfinityRepresentation θ a vacuum =ᵐ[circleMeasure] fun _ => (0 : Fiber) := by
      rw [h]
      exact Lp.coeFn_zero _ _ _
    apply Lp.ext
    filter_upwards [lInfinityRepresentation_coordinate_ae θ a vacuum,
      Lp.coeFn_const 2 circleMeasure (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber), hout,
      Lp.coeFn_zero ℂ ∞ circleMeasure] with x hx hv hz hzero
    have hk := hx 0
    change vacuum x = lp.single 2 (0 : ℤ) (1 : ℂ) at hv
    have ha : a x = 0 := by
      simpa [hz, hv, action, lp.coeFn_single] using hk.symm
    exact ha.trans hzero.symm
  · rintro rfl
    have hz : lInfinityRepresentation θ 0 = 0 := (lInfinityRepresentationCLM θ).map_zero
    rw [hz]
    rfl

theorem lInfinityRepresentation_injective (θ : ℝ) :
    Function.Injective (lInfinityRepresentation θ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (lInfinityRepresentation_vacuum_eq_zero_iff θ (a - b)).mp
  have hzero : lInfinityRepresentation θ (a - b) = 0 := by
    change lInfinityRepresentationCLM θ (a - b) = 0
    rw [map_sub]
    change lInfinityRepresentation θ a - lInfinityRepresentation θ b = 0
    rw [hab, sub_self]
  rw [hzero]
  rfl

theorem vacuumFunctional_lInfinityRepresentation (θ : ℝ)
    (a : Lp ℂ ∞ circleMeasure) :
    vacuumFunctional (lInfinityRepresentation θ a) = ∫ x, a x ∂circleMeasure := by
  change inner ℂ vacuum (lInfinityRepresentation θ a vacuum) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lInfinityRepresentation_coordinate_ae θ a vacuum,
    Lp.coeFn_const 2 circleMeasure (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)]
    with x hx hv
  change vacuum x = lp.single 2 (0 : ℤ) (1 : ℂ) at hv
  rw [hv, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (lInfinityRepresentation θ a vacuum x 0) = a x
  rw [hx, hv]
  simp [action]

theorem lInfinityRepresentation_eq_measurable (θ : ℝ)
    (a : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentation θ a = measurableRepresentation θ
      (LInfinityRepresentative.value a) ‖a‖ (norm_nonneg a)
      (LInfinityRepresentative.stronglyMeasurable_value a).measurable
      (LInfinityRepresentative.norm_value_le a) := by
  apply WeightedShift.fieldDiagonal_congr
  exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

theorem lInfinityRepresentation_mem_algebra (θ : ℝ)
    (a : Lp ℂ ∞ circleMeasure) : lInfinityRepresentation θ a ∈ algebra θ := by
  rw [lInfinityRepresentation_eq_measurable]
  exact measurableRepresentation_mem_algebra θ _ _ _ _ _

theorem U_mul_lInfinityRepresentation_mem_algebra (θ : ℝ)
    (a : Lp ℂ ∞ circleMeasure) : U * lInfinityRepresentation θ a ∈ algebra θ :=
  mul_mem (U_mem_algebra θ) (lInfinityRepresentation_mem_algebra θ a)

theorem lInfinityRepresentation_eq_measurable_of_ae
    (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) (g : Circle → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (heq : a =ᵐ[circleMeasure] g) :
    lInfinityRepresentation θ a = measurableRepresentation θ g C hC hg hb := by
  rw [lInfinityRepresentation_eq_measurable]
  exact measurableRepresentation_congr_ae θ ((LInfinityRepresentative.value_ae a).trans heq)

end Invariant233.Rotation

end

end OAI
