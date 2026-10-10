import OAI.Geometry.IsometricImmersion.Coordinates.CoordinateSwap
import OAI.Geometry.IsometricImmersion.Darboux.DarbouxEquation

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetXX (g : MetricField) (p : Coord) (c : ℝ) (u : Coord) : ℝ :=
  c - jetConnection g p 0 0 u

def solvedDarbouxQ (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 1 1 u + jetNumerator g p b u / jetXX g p c u

theorem jetConnection_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) (u : Coord) :
    jetConnection (swappedMetric g) p i j (coordinateSwap u) =
      jetConnection g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) u := by
  simp only [jetConnection, christoffel_swappedMetric hg hU hp,
    coordinateSwap_apply, Fin.sum_univ_two, swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetMixed_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetMixed (swappedMetric g) p b (coordinateSwap u) =
      jetMixed g (coordinateSwap p) b u := by
  have hs (k : Fin 2) : christoffel g k 1 0 (coordinateSwap p) =
      christoffel g k 0 1 (coordinateSwap p) := christoffel_lower_symm hg hU hp k 1 0
  rw [jetMixed, jetConnection_swappedMetric hg hU hp]
  simp only [swapCoordinateIndex_zero, swapCoordinateIndex_one]
  simp only [jetConnection, hs, jetMixed]

theorem jetYY_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (c : ℝ) (u : Coord) :
    jetYY (swappedMetric g) p c (coordinateSwap u) =
      jetXX g (coordinateSwap p) c u := by
  rw [jetYY, jetConnection_swappedMetric hg hU hp]
  rfl

theorem jetEnergy_swappedMetric (g : MetricField) (p u : Coord) :
    jetEnergy (swappedMetric g) p (coordinateSwap u) =
      jetEnergy g (coordinateSwap p) u := by
  simp only [jetEnergy, swappedMetric_det, swappedMetric_apply, coordinateSwap_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetNumerator_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetNumerator (swappedMetric g) p b (coordinateSwap u) =
      jetNumerator g (coordinateSwap p) b u := by
  rw [jetNumerator, jetMixed_swappedMetric hg hU hp,
    gaussianCurvature_swappedMetric hg hU hp, jetEnergy_swappedMetric]
  rfl

theorem solvedDarboux_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarboux (swappedMetric g) p b c (coordinateSwap u) =
      solvedDarbouxQ g (coordinateSwap p) b c u := by
  rw [solvedDarboux, jetConnection_swappedMetric hg hU hp,
    jetNumerator_swappedMetric hg hU hp, jetYY_swappedMetric hg hU hp]
  rfl

theorem solvedDarbouxQ_eq_swappedP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarbouxQ g p b c u =
      solvedDarboux (swappedMetric g) (coordinateSwap p) b c (coordinateSwap u) := by
  simpa only [coordinateSwap_involutive] using
    (solvedDarboux_swappedMetric hg hU (p := coordinateSwap p) (by simpa using hp) b c u).symm

theorem jetXX_differentiableAt (g : MetricField) (p u : Coord) (c : ℝ) :
    DifferentiableAt ℝ (jetXX g p c) u := by
  change DifferentiableAt ℝ (fun v => c - jetConnection g p 0 0 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) c).sub (jetConnection_differentiableAt g p u 0 0)

theorem coordPartial_jetXX (g : MetricField) (p u : Coord) (c : ℝ) (i : Fin 2) :
    coordPartial i (jetXX g p c) u = -christoffel g i 0 0 p := by
  change coordPartial i (fun v => c - jetConnection g p 0 0 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const c)
    (jetConnection_differentiableAt g p u 0 0) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem solvedDarbouxQ_first_variables_differentiableAt
    (g : MetricField) (p u : Coord) (b c : ℝ) (hxx : jetXX g p c u ≠ 0) :
    DifferentiableAt ℝ (solvedDarbouxQ g p b c) u := by
  have hd := (jetConnection_differentiableAt g p u 1 1).add
    ((jetNumerator_differentiableAt g p u b).mul ((jetXX_differentiableAt g p u c).inv hxx))
  change DifferentiableAt ℝ (fun v =>
    jetConnection g p 1 1 v + jetNumerator g p b v / jetXX g p c v) u
  simpa only [div_eq_mul_inv, Pi.add_def, Pi.mul_def, Pi.inv_def] using hd

theorem solvedDarbouxQ_firstJet_expanded (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetXX g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarbouxQ g p b c) u =
      christoffel g i 1 1 p - 2 * (jetMixed g p b u / jetXX g p c u) * christoffel g i 0 1 p +
        (jetMixed g p b u / jetXX g p c u) ^ 2 * christoffel g i 0 0 p +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetXX g p c u +
            jetEnergy g p u * christoffel g i 0 0 p / (jetXX g p c u) ^ 2) := by
  have hN := jetNumerator_differentiableAt g p u b
  have hH := jetXX_differentiableAt g p u c
  have hQ : DifferentiableAt ℝ
      (fun v => jetNumerator g p b v / jetXX g p c v) u := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (hN.hasFDerivAt.fun_mul
        ((hasDerivAt_inv hne).comp_hasFDerivAt u hH.hasFDerivAt)).differentiableAt
  change coordPartial i (fun v => jetConnection g p 1 1 v +
    jetNumerator g p b v / jetXX g p c v) u = _
  rw [HessianCalculus.coordPartial_add_at (jetConnection_differentiableAt g p u 1 1) hQ i,
    coordPartial_jetConnection, coordPartial_div hN hH hne i,
    coordPartial_jetNumerator, coordPartial_jetXX]
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem solvedDarbouxQ_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p t c u) b =
      2 * (jetMixed g p b u / jetXX g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetXX g p c u)).const_add
      (jetConnection g p 1 1 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetXX g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarbouxQ_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p b t u) c =
      -((jetMixed g p b u / jetXX g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetXX g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 0 0 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 1 1 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    jetNumerator g p b u / (t - jetConnection g p 0 0 u)) c = _
  rw [hd.deriv]
  change (0 * jetXX g p c u - jetNumerator g p b u * 1) / (jetXX g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem jetXX_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetXX g p (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 0 := rfl

theorem solvedDarbouxQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    apply (eq_div_iff hxx).2
    nlinarith [hdet]
  change coordPartial 1 (coordPartial 1 z) p -
    jetConnection g p 1 1 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

theorem darbouxDet_of_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p)) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p := by
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z] at hQ
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    change coordPartial 1 (coordPartial 1 z) p -
      jetConnection g p 1 1 (fun i => coordPartial i z p) = _
    linarith [hQ]
  have hmul := (eq_div_iff hxx).1 hsolve
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    nlinarith [hmul]
  simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hdet

theorem darbouxDet_iff_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p =
        solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
          (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) :=
  ⟨solvedDarbouxQ_at_height hg hU hz hp hxx,
    darbouxDet_of_solvedQ_at_height hg hU hz hp hxx⟩

end SmoothLocal.Geometry

end

end OAI
