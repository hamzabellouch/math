import OAI.Geometry.IsometricImmersion.Darboux.QResidualActive
import OAI.Geometry.IsometricImmersion.Metrics.MetricPBundleBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

abbrev QSpatialState := Fin 5 → ℝ

def qSpatialAxis : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]
def qSpatialIndex : Fin 6 → Fin 5 := ![0, 0, 1, 2, 3, 4]

def qSpatialLinear : QSpatialState →ₗ[ℝ] DarbouxState where
  toFun v := ![v 0, 0, v 1, v 2, v 3, v 4]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def qSpatialCLM : QSpatialState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qSpatialLinear

def qFixedTimeState (theta : ℝ) (v : QSpatialState) : DarbouxState :=
  qSpatialCLM v + Pi.single 1 theta

def qSpatialProjection (w : DarbouxState) : QSpatialState := ![w 0, w 2, w 3, w 4, w 5]

def qFixedTimeQ (g : MetricField) (theta : ℝ) : QSpatialState → ℝ :=
  sixVariableQ g ∘ qFixedTimeState theta

def qFixedTimeDomain (g : MetricField) (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  qFixedTimeState theta ⁻¹' darbouxQStateDomain g U

theorem qSpatialAxis_index {i : Fin 6} (hi : i ≠ 1) : qSpatialAxis (qSpatialIndex i) = i := by
  fin_cases i <;> first | rfl | exact (hi rfl).elim

theorem qSpatialCLM_single (i : Fin 5) :
    qSpatialCLM (Pi.single i 1) = Pi.single (qSpatialAxis i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [qSpatialCLM, qSpatialLinear, qSpatialAxis]

theorem qFixedTimeState_projection (w : DarbouxState) :
    qFixedTimeState (w 1) (qSpatialProjection w) = w := by
  ext i
  fin_cases i <;> simp [qFixedTimeState, qSpatialProjection, qSpatialCLM,
    qSpatialLinear]

theorem qFixedTimeState_contDiff (theta : ℝ) : ContDiff ℝ ∞ (qFixedTimeState theta) :=
  qSpatialCLM.contDiff.add contDiff_const

theorem qFixedTimeDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeDomain g U theta) :=
  (darbouxQStateDomain_isOpen hg hU).preimage (qFixedTimeState_contDiff theta).continuous

theorem qFixedTimeQ_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    ContDiffOn ℝ ∞ (qFixedTimeQ g theta) (qFixedTimeDomain g U theta) :=
  (sixVariableQ_contDiffOn hg hU).comp (qFixedTimeState_contDiff theta).contDiffOn
    (fun _ hv => hv)

theorem qFixedTimeQ_iteratedFDeriv
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta) (n : ℕ) :
    iteratedFDeriv ℝ n (qFixedTimeQ g theta) v =
      (iteratedFDeriv ℝ n (sixVariableQ g) (qFixedTimeState theta v)).compContinuousLinearMap
        (fun _ => qSpatialCLM) := by
  let c : DarbouxState := Pi.single 1 theta
  let O : Set DarbouxState := (fun w : DarbouxState => w + c) ⁻¹' darbouxQStateDomain g U
  have hO : IsOpen O := (darbouxQStateDomain_isOpen hg hU).preimage (by fun_prop)
  have hF : ContDiffOn ℝ ∞ (fun w : DarbouxState => sixVariableQ g (w + c)) O :=
    (sixVariableQ_contDiffOn hg hU).comp (by fun_prop) (fun _ hw => hw)
  have hpre : IsOpen (qSpatialCLM ⁻¹' O) := hO.preimage qSpatialCLM.continuous
  have hp : qSpatialCLM v ∈ O := hv
  have he := qSpatialCLM.iteratedFDerivWithin_comp_right hF hO.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hO hp,
    iteratedFDeriv_comp_add_right n c (qSpatialCLM v)] at he
  exact he

theorem qCoordinateChainCoefficient_eq_fixedTime
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    qCoordinateChainCoefficient g z w r p =
      iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        (fun i => Pi.single (qSpatialIndex (r i)) 1) := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv w.arity,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  unfold qCoordinateChainCoefficient
  congr 1
  funext i
  rw [qSpatialCLM_single, qSpatialAxis_index (hactive i).1]

theorem qCoordinateChainCoefficient_abs_le_fixedTime_derivative
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    |qCoordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ := by
  rw [qCoordinateChainCoefficient_eq_fixedTime hg hU hp hxx w r hactive, ← Real.norm_eq_abs]
  have hb := (iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      (fun i => Pi.single (qSpatialIndex (r i)) (1 : ℝ))
  simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using hb

end SmoothLocal.HighEquation

end

end OAI
