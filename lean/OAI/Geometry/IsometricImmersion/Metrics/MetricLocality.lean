import OAI.Geometry.IsometricImmersion.Metric
import OAI.Geometry.IsometricImmersion.Energy.HeightEnergy
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Matrix.Normed

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem coordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f =ᶠ[𝓝 p] coordPartial i h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact coordPartial_eq_of_eventuallyEq hq i

def iteratedCoordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Fin 2) → (Coord → V) → Coord → V
  | [], f => f
  | i :: is, f => coordPartial i (iteratedCoordPartial is f)

theorem iteratedCoordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs f =ᶠ[𝓝 p] iteratedCoordPartial dirs h := by
  induction dirs with
  | nil => exact heq
  | cons i is ih => exact coordPartial_eventuallyEq ih i

theorem iteratedCoordPartial_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (dirs : List (Fin 2)) : iteratedCoordPartial dirs (0 : Coord → V) = 0 := by
  induction dirs with
  | nil => rfl
  | cons i is ih =>
      change coordPartial i (iteratedCoordPartial is (0 : Coord → V)) = 0
      rw [ih]
      funext p
      change fderiv ℝ (fun _ : Coord => (0 : V)) p (Pi.single i 1) = 0
      simp

theorem eventuallyEq_zero_of_not_mem_tsupport
    {V : Type*} [Zero V] (f : Coord → V) {p : Coord} (hp : p ∉ tsupport f) :
    f =ᶠ[𝓝 p] 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hp] with q hq
  change f q = 0
  by_contra hne
  exact hq (subset_tsupport f hne)

theorem iteratedCoordPartial_zero_of_not_mem_tsupport
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) {p : Coord} (hp : p ∉ tsupport f) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs f p = 0 := by
  have heq := iteratedCoordPartial_eventuallyEq
    (eventuallyEq_zero_of_not_mem_tsupport f hp) dirs
  rw [heq.self_of_nhds, iteratedCoordPartial_zero]
  rfl

theorem metric_coeff_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (i j : Fin 2) :
    (fun q => g q i j) =ᶠ[𝓝 p] (fun q => h q i j) :=
  heq.mono fun _ hq => congrFun (congrFun hq i) j

theorem christoffel_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  have hval := heq.self_of_nhds
  have hd (a b c : Fin 2) : coordPartial a (fun q => g q b c) p =
      coordPartial a (fun q => h q b c) p :=
    coordPartial_eq_of_eventuallyEq (metric_coeff_eventuallyEq heq b c) a
  simp only [christoffel, inverseMetric, hval, hd]

theorem christoffel_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j =ᶠ[𝓝 p] christoffel h k i j :=
  heq.eventuallyEq_nhds.mono fun _ hq => christoffel_eq_of_eventuallyEq hq k i j

theorem riemann_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (l k i j : Fin 2) :
    riemann g l k i j p = riemann h l k i j p := by
  have hΓ := christoffel_eq_of_eventuallyEq heq
  have hd (a b c d : Fin 2) : coordPartial a (christoffel g b c d) p =
      coordPartial a (christoffel h b c d) p :=
    coordPartial_eq_of_eventuallyEq (christoffel_eventuallyEq heq b c d) a
  simp only [riemann, hΓ, hd]

theorem gaussianCurvature_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) : gaussianCurvature g p = gaussianCurvature h p := by
  simp only [gaussianCurvature, heq.self_of_nhds, riemann_eq_of_eventuallyEq heq]

theorem covHessian_eq_of_metric_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (z : Coord → ℝ) : covHessian g z p = covHessian h z p := by
  ext i j
  simp only [covHessian, christoffel_eq_of_eventuallyEq heq]

theorem heightEnergy_eq_of_metric_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (z : Coord → ℝ) : heightEnergy g z p = heightEnergy h z p := by
  simp only [heightEnergy, covectorNormSq, inverseMetric, heq.self_of_nhds]

theorem metric_add_eventuallyEq_of_not_mem_tsupport (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) : g + η =ᶠ[𝓝 p] g := by
  filter_upwards [eventuallyEq_zero_of_not_mem_tsupport η hp] with q hq
  change g q + η q = g q
  simp only [hq, Pi.zero_apply, add_zero]

theorem metric_add_all_coordinate_jets (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs (g + η) p = iteratedCoordPartial dirs g p :=
  (iteratedCoordPartial_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g η hp) dirs).self_of_nhds

theorem gaussianCurvature_add_eq_off_tsupport (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) :
    gaussianCurvature (g + η) p = gaussianCurvature g p :=
  gaussianCurvature_eq_of_eventuallyEq (metric_add_eventuallyEq_of_not_mem_tsupport g η hp)

end SmoothLocal.Geometry

end

end OAI
