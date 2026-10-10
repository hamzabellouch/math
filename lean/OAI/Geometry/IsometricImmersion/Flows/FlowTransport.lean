import OAI.Geometry.IsometricImmersion.Flows.FlowCurvature
import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftEquation
import OAI.Geometry.IsometricImmersion.Darboux.TransverseCoefficient

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def capPullback (Y : ℝ → ℝ → ℝ) (u : Coord → ℝ) : Coord → ℝ := fun p => u (capChart Y p)

def capChartSigma (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
    (coordPartial 1 (capFlowHeight Y) p) ^ 3

def capTransportA (Y : ℝ → ℝ → ℝ) (a : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * (capChartRho Y p) ^ 2

def capTransportC (Y : ℝ → ℝ → ℝ) (a C0 : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * capChartSigma Y p + capPullback Y C0 p * capChartRho Y p

def driftOperator (q a B C0 u : Coord → ℝ) (p : Coord) : ℝ :=
  coordinateDrift q (coordinateDrift q u) p + a p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordinateDrift q u p + C0 p * coordPartial 1 u p

variable {Y : ℝ → ℝ → ℝ} {u q : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem capChart_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capChart Y) p =
      (if i = 0 then Pi.single 0 (1 : ℝ) else 0) +
        coordPartial i (capFlowHeight Y) p • Pi.single 1 (1 : ℝ) := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd : HasFDerivAt (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
      capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord))
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 0 (1 : ℝ) : Coord) +
        (fderiv ℝ (capFlowHeight Y) p).smulRight (Pi.single 1 (1 : ℝ) : Coord)) p :=
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      (hheight.hasFDerivAt.smul_const (Pi.single 1 (1 : ℝ) : Coord))
  change fderiv ℝ (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
    capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord)) p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]

theorem capPullback_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (capPullback Y u) capChartDomain :=
  hu.comp (capChart_contDiffOn hY) hmap

theorem capPullback_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) (i : Fin 2) :
    coordPartial i (capPullback Y u) p =
      (if i = 0 then coordPartial 0 u (capChart Y p) else 0) +
        coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hchart : DifferentiableAt ℝ (capChart Y) p :=
    ((capChart_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  change fderiv ℝ (u ∘ capChart Y) p (Pi.single i 1) = _
  rw [fderiv_comp p hu hchart, ContinuousLinearMap.comp_apply]
  change fderiv ℝ u (capChart Y p) (coordPartial i (capChart Y) p) = _
  rw [capChart_partial hY hp i]
  fin_cases i <;> simp [coordPartial, smul_eq_mul] <;> ring

theorem capPullback_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 1 (capPullback Y u) p =
      capPullback Y (coordPartial 1 u) p * coordPartial 1 (capFlowHeight Y) p := by
  simpa only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, zero_add, capPullback] using
    capPullback_partial hY hp hu 1

theorem capPullback_partial_time
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 0 (capPullback Y u) p = coordinateDrift q u (capChart Y p) := by
  rw [capPullback_partial hY hp hu 0, capFlowHeight_partial_time hY hode hp]
  simp only [↓reduceIte, coordinateDrift]
  ring

theorem capPullback_original_y
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    capPullback Y (coordPartial 1 u) p = capChartRho Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_partial_initial hY hp hu, capChartRho]
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']

theorem capPullback_second_initial_forward
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
      capPullback Y (coordPartial 1 (coordPartial 1 u)) p *
          (coordPartial 1 (capFlowHeight Y) p) ^ 2 +
        capPullback Y (coordPartial 1 u) p * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p := by
  have huy := partial_contDiffOn hu hU 1
  have hPuy := capPullback_contDiffOn hY huy hmap
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  have he : coordPartial 1 (capPullback Y u) =ᶠ[𝓝 p]
      (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_initial hY hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by simp))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 1 (1 : ℝ))) he.fderiv_eq
  change coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
    coordPartial 1 (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) p at hd
  rw [hd, HessianCalculus.coordPartial_mul_at
    ((hPuy.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)) 1,
    capPullback_partial_initial hY hp
      ((huy.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  ring

theorem capPullback_original_yy
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordPartial 1 (coordPartial 1 u)) p =
      (capChartRho Y p) ^ 2 * coordPartial 1 (coordPartial 1 (capPullback Y u)) p +
        capChartSigma Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_second_initial_forward hY hu hU hmap hp,
    capPullback_partial_initial hY hp
      ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
  ring

theorem coordinateDrift_contDiffOn (hq : ContDiffOn ℝ ∞ q U)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (coordinateDrift q u) U :=
  (partial_contDiffOn hu hU 0).sub (hq.mul (partial_contDiffOn hu hU 1))

theorem capPullback_drift_twice
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordinateDrift q (coordinateDrift q u)) p =
      coordPartial 0 (coordPartial 0 (capPullback Y u)) p := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  have he : coordPartial 0 (capPullback Y u) =ᶠ[𝓝 p] capPullback Y (coordinateDrift q u) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_time hY hode hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by simp))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 0 (1 : ℝ))) he.fderiv_eq
  change coordPartial 0 (coordPartial 0 (capPullback Y u)) p =
    coordPartial 0 (capPullback Y (coordinateDrift q u)) p at hd
  rw [hd, capPullback_partial_time hY hode hp
    ((hDu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  rfl

theorem capChartRho_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capChartRho Y) p =
      -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p) ^ 2 := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  change coordPartial 1 (fun z => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) z) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    (capFlowHeight_partial_initial_pos hY hvar hp).ne' 1]
  simp [coordPartial]

theorem capChartSigma_eq_rho_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) :
    capChartSigma Y p = capChartRho Y p * coordPartial 1 (capChartRho Y) p := by
  rw [capChartRho_partial_initial hY hvar hp]
  unfold capChartSigma capChartRho
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']

theorem capChartSigma_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartSigma Y) capChartDomain := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  exact (partial_contDiffOn hYs capChartDomain_isOpen 1).neg.div (hYs.pow 3)
    (fun p hp => pow_ne_zero 3 (capFlowHeight_partial_initial_pos hY hvar hp).ne')

theorem capTransportA_partial_initial {a : Coord → ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (capTransportA Y a) p =
      capChartRho Y p * capPullback Y (coordPartial 1 a) p +
        2 * capPullback Y a p * capChartSigma Y p := by
  have hPa : DifferentiableAt ℝ (capPullback Y a) p :=
    ((capPullback_contDiffOn hY ha hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hrho : DifferentiableAt ℝ (capChartRho Y) p :=
    ((capChartRho_contDiffOn hY hvar).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  unfold capTransportA
  simp only [pow_two]
  have hrhorho : DifferentiableAt ℝ (fun z => capChartRho Y z * capChartRho Y z) p :=
    hrho.mul hrho
  rw [HessianCalculus.coordPartial_mul_at hPa hrhorho 1,
    HessianCalculus.coordPartial_mul_at hrho hrho 1,
    capPullback_partial_initial hY hp
      ((ha.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)),
    capChartRho_partial_initial hY hvar hp]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
  ring

theorem cap_driftOperator_transport (a B C0 : Coord → ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (driftOperator q a B C0 u) p =
      multiplierOperator (capTransportA Y a) (capPullback Y B)
        (capTransportC Y a C0) (capPullback Y u) p := by
  have hud := ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))
  change capPullback Y (coordinateDrift q (coordinateDrift q u)) p +
    a (capChart Y p) * capPullback Y (coordPartial 1 (coordPartial 1 u)) p +
    B (capChart Y p) * coordinateDrift q u (capChart Y p) +
    C0 (capChart Y p) * capPullback Y (coordPartial 1 u) p = _
  rw [capPullback_drift_twice hY hode hq hu hU hmap hp,
    capPullback_original_yy hY hvar hu hU hmap hp,
    ← capPullback_partial_time hY hode hp hud,
    capPullback_original_y hY hvar hp hud]
  unfold multiplierOperator capTransportA capTransportC capPullback
  ring

end SmoothLocal.Flow

end

end OAI
