import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Extensions
import OAI.Geometry.IntegralFillings.Jacobian.Coordinates
import OAI.Geometry.IntegralFillings.Charts.LinearMass
import OAI.Geometry.IntegralFillings.Charts.CurrentContinuity

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma scalar_linear (b c : X → ℝ) (a d : ℝ) :
    C.scalar (fun x => a*b x+d*c x) = fun z => a*C.scalar b z+d*C.scalar c z := by
  funext z
  by_cases hz : z ∈ C.domain <;> simp [scalar,hz]

lemma action_linearFirst (b c : X → ℝ) (π : Fin k → X → ℝ) (a d : ℝ)
    (hb : BoundedLip b) (hc : BoundedLip c)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.action (fun x => a*b x+d*c x) π = a*C.action b π+d*C.action c π := by
  have hab : Admissible (fun x => a*b x+d*c x) π :=
    ⟨(hb.const_mul a).add (hc.const_mul d),hπ⟩
  rw [action,ite_eq_left hab,action,ite_eq_left ⟨hb,hπ⟩,action,ite_eq_left ⟨hc,hπ⟩,C.scalar_linear]
  have heq : (fun z => (C.multiplicity z : ℝ) * (a*C.scalar b z+d*C.scalar c z) * C.jacobian π z) =
      fun z => a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar c z*C.jacobian π z) := by funext z; ring
  rw [heq,integral_add ((C.integrable_action_integrand hb hπ).const_mul a)
    ((C.integrable_action_integrand hc hπ).const_mul d),integral_const_mul,integral_const_mul]

lemma ae_jacobian_linear (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (a d : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => a*π i x+d*f x)) z =
        a*C.jacobian π z+d*C.jacobian (Function.update π i f) z := by
  obtain ⟨K,hK⟩ := hπ i
  obtain ⟨L,hL⟩ := hf
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,C.ae_differentiableWithinAt_scalar hK,
    C.ae_differentiableWithinAt_scalar hL] with z hz hdπ hdf
  have hd : fderivWithin ℝ (C.scalar (fun x => a*π i x+d*f x)) C.domain z =
      a • fderivWithin ℝ (C.scalar (π i)) C.domain z +
        d • fderivWithin ℝ (C.scalar f) C.domain z := by
    rw [C.scalar_linear]
    exact ((hdπ.hasFDerivWithinAt.const_mul a).add (hdf.hasFDerivWithinAt.const_mul d)).fderivWithin hz
  rw [C.jacobian_update,C.jacobian_update]
  simp only [hd,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun l j =>
    fderivWithin ℝ (C.scalar (π l)) C.domain z (EuclideanSpace.single j 1)
  let w : Fin k → ℝ := fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1)
  change (M.updateRow i (a • M i+d • w)).det = a*M.det+d*(M.updateRow i w).det
  rw [Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self]

lemma action_linearCoord (b : X → ℝ) (π : Fin k → X → ℝ) (i : Fin k)
    (f : X → ℝ) (a d : ℝ) (h : Admissible b π)
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    C.action b (Function.update π i (fun x => a*π i x+d*f x)) =
      a*C.action b π+d*C.action b (Function.update π i f) := by
  have hup {g : X → ℝ} (hg : ∃ K : ℝ≥0, LipschitzWith K g) :
      Admissible b (Function.update π i g) := by
    refine ⟨h.1,fun j => ?_⟩
    by_cases hji : j=i
    · simpa [hji] using hg
    · simpa [hji] using h.2 j
  have hg : ∃ K : ℝ≥0, LipschitzWith K (fun x => a*π i x+d*f x) := by
    obtain ⟨K,hK⟩ := h.2 i
    obtain ⟨L,hL⟩ := hf
    refine ⟨‖a‖₊ * K + ‖d‖₊ * L,?_⟩
    simpa only [Function.comp_def,smul_eq_mul] using
      ((lipschitzWith_smul a).comp hK).add ((lipschitzWith_smul d).comp hL)
  rw [action,ite_eq_left (hup hg),action,ite_eq_left h,action,ite_eq_left (hup hf)]
  calc
    _ = ∫ z in C.domain, a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian (Function.update π i f) z) := by
      apply integral_congr_ae
      filter_upwards [C.ae_jacobian_linear π i f a d h.2 hf] with z hz
      rw [hz]; ring
    _ = _ := by
      rw [integral_add ((C.integrable_action_integrand h.1 h.2).const_mul a)
        ((C.integrable_action_integrand h.1 (hup hf).2).const_mul d),
        integral_const_mul,integral_const_mul]

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma continuousOn_paramExtended : ContinuousOn C.paramExtended C.domain := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  have hl : LipschitzOnWith L C.paramExtended C.domain := by
    apply lipschitzOnWith_iff_restrict.mpr
    convert hφ using 1
    funext z
    simp [paramExtended,z.2]
  exact hl.continuousOn

lemma action_locality (b : X → ℝ) (π : Fin k → X → ℝ) (h : Admissible b π)
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) : C.action b π = 0 := by
  obtain ⟨i,U,c,hU,hb,hπ⟩ := hloc
  rw [action,ite_eq_left h]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem C.borel] with z hz
  by_cases hbz : C.scalar b z = 0
  · simp [hbz]
  have hext : C.paramExtended z = C.param ⟨z,hz⟩ := by simp [paramExtended,hz]
  have hzU : C.paramExtended z ∈ U := by
    rw [hext]
    apply hb
    simpa [Function.mem_support,C.scalar_eq hz] using hbz
  have hh := (C.continuousOn_paramExtended z hz).preimage_mem_nhdsWithin (hU.mem_nhds hzU)
  have heq : C.scalar (π i) =ᶠ[𝓝[C.domain] z] fun _ => c := by
    filter_upwards [hh,eventually_mem_nhdsWithin] with y hy hys
    rw [C.scalar_eq hys]
    have hye : C.paramExtended y = C.param ⟨y,hys⟩ := by simp [paramExtended,hys]
    exact hπ _ (hye ▸ hy)
  have heqz : C.scalar (π i) z = c := by rw [C.scalar_eq hz]; exact hπ _ (hext ▸ hzU)
  have hd := heq.fderivWithin_eq (𝕜 := ℝ) heqz
  have hd0 : fderivWithin ℝ (C.scalar (π i)) C.domain z = 0 := by
    exact hd.trans (by
      simpa only [Function.const_def,Pi.zero_apply] using
        congrFun (fderivWithin_const (𝕜 := ℝ) (E := Euc k) (s := C.domain) c) z)
  have hdet : C.jacobian π z = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    change fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1) = 0
    rw [hd0]; rfl
  rw [hdet,mul_zero]; rfl

variable [MeasurableSpace X] [BorelSpace X]
lemma action_finiteMass : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls C.action μ := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  obtain ⟨B,hB,hdet⟩ := coordinateJacobian_uniform_bound L
    (fun j : Fin k => EuclideanSpace.single j (1 : ℝ))
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * B) (volume.restrict C.domain) :=
    C.integrable.abs.mul_const B
  refine ⟨C.majorantMeasure (fun _ => B),densityPush_finite _ _ hρ,?_⟩
  apply C.majorant_controls hρ (Eventually.of_forall fun _ => hB)
  intro π hπ
  have hs (i : Fin k) : LipschitzOnWith L (C.scalar (π i)) C.domain := by
    simpa only [one_mul] using C.scalar_lipschitzOn hφ (hπ i)
  choose F hF heq using fun i => (hs i).extend_real
  filter_upwards [C.ae_jacobian_eq_extensions hF heq] with z hz
  have H := hdet F hF z
  rw [hz]
  have heqdet : Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) =
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
    rw [coordinateJacobian,← Matrix.det_transpose]; rfl
  simpa only [heqdet,Real.norm_eq_abs] using H

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

lemma action_isMetricCurrent : IsMetricCurrent C.action := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have hd : C.domain = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact isEmptyElim (C.param ⟨z,hz⟩)
    have heq : C.action = fun _ _ => 0 := by
      funext b π
      simp [action,hd]
    rw [heq]
    exact isMetricCurrent_zero _
  · exact {
      offDomain := by intro b π h; simp [action,h]
      linearFirst := C.action_linearFirst
      linearCoord := C.action_linearCoord
      sequentialContinuity := C.action_sequentialContinuity
      locality := C.action_locality
      finiteMass := C.action_finiteMass }

end SharpIntegralFillings.IntegerChart

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end

end OAI
