import OAI.AlgebraicGeometry.PlaneCurves.ChartGradients
import OAI.AlgebraicGeometry.PlaneCurves.CubicEquations
import OAI.AlgebraicGeometry.PlaneCurves.MarkedDisplacements
import OAI.AlgebraicGeometry.PlaneCurves.UniversalSections

namespace OAI

/-!
# Marked cubic charts, multipliers, coordinate compatibility, and smooth geometry
-/

section

/-! Literal multiplier equalities in the fixed covering frames. No change by an
isomorphic presentation or reduction of any exponent modulo integers is made. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05
open scoped BigOperators

@[simp] theorem rayPoint_zero (τ : ℝ) : rayPoint τ 0 = 1 := by
  apply Units.ext
  simp [rayPoint]

theorem rayPoint_add (τ a b : ℝ) : rayPoint τ (a + b) = rayPoint τ a * rayPoint τ b := by
  apply Units.ext
  simp only [rayPoint, Units.val_mk0, Units.val_mul, add_mul, Complex.ofReal_add,
    Complex.exp_add]

theorem rayPoint_nat_mul (τ s : ℝ) (n : ℕ) : rayPoint τ ((n : ℝ) * s) = rayPoint τ s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul, rayPoint_add, ih, pow_succ]

theorem rayPoint_sum {ι : Type*} (τ : ℝ) (s : Finset ι) (x : ι → ℝ) :
    rayPoint τ (∑ i ∈ s, x i) = ∏ i ∈ s, rayPoint τ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, rayPoint_add, ih]

/-- The nine-point theta multiplier is exactly -τ^(sum x_i) in the chosen frame. -/
theorem piMultiplier_eq_neg_rayPoint_sum (τ : ℝ) (xi : Fin 9 → ℝ) :
    piMultiplier τ xi = -(rayPoint τ (∑ i, xi i)) := by
  apply Units.ext
  rw [piMultiplier_coe, Nagata.W08.markedThetaMultiplier_nine, rayPoint_sum]
  simp

/-- The normal-bundle multiplier is the literal cube τ^(3η). -/
theorem normalMultiplier_eq_rayPoint (τ η : ℝ) :
    rayPoint τ η ^ 3 = rayPoint τ (3 * η) := by
  simpa using (rayPoint_nat_mul τ η 3).symm

/-- Exact A multiplier from the source relation 3η=sum(x_i)+rhoStar. -/
theorem sourceAMultiplier (τ η rhoStar : ℝ) (xi : Fin 9 → ℝ)
    (hη : 3 * η = (∑ i, xi i) + rhoStar) :
    rayPoint τ η ^ 3 / piMultiplier τ xi = -(rayPoint τ rhoStar) := by
  rw [normalMultiplier_eq_rayPoint, hη, rayPoint_add, piMultiplier_eq_neg_rayPoint_sum]
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg]
  field_simp

/-- The source's unreduced exponent eta satisfies the required multiplier identity. -/
theorem sourceAMultiplier_eta (τ rhoStar : ℝ) (xi : Fin 9 → ℝ) :
    rayPoint τ (((∑ i, xi i) + rhoStar) / 3) ^ 3 / piMultiplier τ xi =
      -(rayPoint τ rhoStar) := by
  apply sourceAMultiplier
  ring

end Nagata.W06.TorusConfiguration

end
end

section

noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W07 Nagata.W21 Nagata.ProjectiveGeometry Nagata.W16

/-- Actual degree-three theta evaluation vector at each selected covering lift. -/
def actualMarkedVector {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : Fin 3 → ℂ :=
  cubicEvaluationVector (actualCubicBasis hτ hτone (rayPoint τ η).ne_zero)
    (coverTuple τ x0 xi ξ t : ℂ)

theorem actualMarkedVector_ne_zero {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    actualMarkedVector hτ hτone η x0 xi ξ t ≠ 0 :=
  cubicEvaluationVector_ne_zero _ (actualCubic_eval_kernel_dimension hτ hτone
    (rayPoint τ η).ne_zero (coverTuple τ x0 xi ξ t).ne_zero)

/-- The actual cubic-map point, with multiplier exactly τ^η. -/
def actualMarkedPoint {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : PlanePoint :=
  actualCubicMap hτ hτone (rayPoint τ η).ne_zero (torusTuple τ hτ x0 xi ξ t)

/-- The actual selected evaluation vector represents the actual projective point. -/
theorem actualMarkedPoint_eq_mk {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    actualMarkedPoint hτ hτone η x0 xi ξ t =
      Projectivization.mk ℂ (actualMarkedVector hτ hτone η x0 xi ξ t)
        (actualMarkedVector_ne_zero hτ hτone η x0 xi ξ t) := rfl

theorem actualMarkedPoint_injective {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) :
    Function.Injective (actualMarkedPoint hτ hτone η x0 xi ξ) :=
  (actualCubicMap_injective hτ hτone (rayPoint τ η).ne_zero).comp hinj

/-- Actual ordered distinct points with the cubic embedding premise discharged. -/
def actualMarkedConfiguration {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) : OrderedDistinctPoints (9 + q) :=
  ⟨actualMarkedPoint hτ hτone η x0 xi ξ,
    actualMarkedPoint_injective hτ hτone η x0 xi ξ hinj⟩

/-- Exact r=9+q reindexing of the actual cubic configuration. -/
def actualMarkedConfigurationOfEq {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η x0 : ℝ) (xi : Fin 9 → ℝ)
    (ξ : Fin q → ℂ) (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) :
    OrderedDistinctPoints r :=
  reindexConfiguration hr (actualMarkedConfiguration hτ hτone η x0 xi ξ hinj)

/-- Every indexed actual point has its specified homogeneous evaluation vector. -/
theorem actualMarkedConfigurationOfEq_apply {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η x0 : ℝ) (xi : Fin 9 → ℝ)
    (ξ : Fin q → ℂ) (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) (i : Fin r) :
    (actualMarkedConfigurationOfEq hr hτ hτone η x0 xi ξ hinj).val i =
      Projectivization.mk ℂ (actualMarkedVector hτ hτone η x0 xi ξ (Fin.cast hr i))
        (actualMarkedVector_ne_zero hτ hτone η x0 xi ξ (Fin.cast hr i)) := rfl

@[simp] theorem actualMarkedVector_left {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    actualMarkedVector hτ hτone η x0 xi ξ (finSumFinEquiv (Sum.inl i)) =
      cubicEvaluationVector (actualCubicBasis hτ hτone (rayPoint τ η).ne_zero)
        (rayPoint τ (xi i) : ℂ) := by
  unfold actualMarkedVector
  rw [coverTuple_left]

@[simp] theorem actualMarkedVector_right {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (j : Fin q) :
    actualMarkedVector hτ hτone η x0 xi ξ (finSumFinEquiv (Sum.inr j)) =
      cubicEvaluationVector (actualCubicBasis hτ hτone (rayPoint τ η).ne_zero)
        (chartPoint τ x0 (ξ j) : ℂ) := by
  unfold actualMarkedVector
  rw [coverTuple_right]

/-- One actual nonzero cubic equation vanishes on all the marked evaluation vectors.
The equation comes from the complete actual map, independently of q and its marks. -/
theorem exists_actualMarkedCubicForm {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η : ℝ) :
    ∃ G : NonzeroHomogeneousForm 3, ∀ (x0 : ℝ) (xi : Fin 9 → ℝ)
      (q : ℕ) (ξ : Fin q → ℂ) (t : Fin (9 + q)),
      MvPolynomial.eval (actualMarkedVector hτ hτone η x0 xi ξ t) G.polynomial = 0 := by
  obtain ⟨G, hG⟩ := exists_actualCubicForm hτ hτone (rayPoint τ η).ne_zero
  exact ⟨G, fun x0 xi q ξ t => hG _ (coverTuple τ x0 xi ξ t).ne_zero⟩

/-- Every real period supports every finite nearby configuration on the actual
projective cubic map. No map, basis, dimension or embedding assumption is supplied. -/
theorem exists_actualMarkedConfiguration_disk {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η : ℝ) (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℕ) (ξ : Fin q → ℂ),
      Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
      ∃ p : OrderedDistinctPoints (9 + q),
        (∀ t, p.val t = actualMarkedPoint hτ hτone η (1 / 2) xi ξ t) ∧
        ∀ j, markedPi τ xi (chartPoint τ (1 / 2) (ξ j) : ℂ) ≠ 0 := by
  obtain ⟨R, hR, hcfg⟩ := exists_disk_for_fixed_period hτ hτone xi hxi hxi_bounds
  refine ⟨R, hR, ?_⟩
  intro q ξ hξ hξR
  obtain ⟨hinj, hPi⟩ := hcfg q ξ hξ hξR
  exact ⟨actualMarkedConfiguration hτ hτone η (1 / 2) xi ξ hinj, fun _ => rfl, hPi⟩

end Nagata.W06.TorusConfiguration

end
end

section

/-! Exact actual cubic coordinate functions and affine normal-chart input.
The partial derivative needed for a normal chart is deliberately not asserted. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W07 Nagata.W08 Nagata.W21 Nagata.ProjectiveGeometry
open Nagata.Workers.W17 Nagata.Workers.W28

/-- The three actual holomorphic multiplier sections defining the genuine map. -/
def actualCoordinateSections {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η : ℝ) :
    Fin 3 → automorphicSections (τ : ℂ) 3 (rayPoint τ η : ℂ) :=
  actualCubicBasis hτ hτone (rayPoint τ η).ne_zero

/-- Literal covering-space coordinate functions; no representative choices enter. -/
def actualCoordinateFunctions {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η : ℝ) :
    Fin 3 → ℂ → ℂ := fun a => (actualCoordinateSections hτ hτone η a).val

theorem actualCoordinateFunctions_analyticAt {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η : ℝ) (a : Fin 3) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (actualCoordinateFunctions hτ hτone η a) z :=
  automorphicSection_analyticAt (actualCoordinateSections hτ hτone η a) hz

@[simp] theorem actualMarkedVector_coordinate {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) (a : Fin 3) :
    actualMarkedVector hτ hτone η x0 xi ξ t a =
      actualCoordinateFunctions hτ hτone η a (coverTuple τ x0 xi ξ t : ℂ) := rfl

theorem exists_actualMarkedChart {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    ∃ c : Fin 3, actualCoordinateFunctions hτ hτone η c (coverTuple τ x0 xi ξ t : ℂ) ≠ 0 := by
  by_contra! h
  apply actualMarkedVector_ne_zero hτ hτone η x0 xi ξ t
  funext a
  exact h a

/-- A genuine nonzero homogeneous coordinate is chosen at every actual marked point. -/
def actualMarkedChart {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : Fin 3 :=
  Classical.choose (exists_actualMarkedChart hτ hτone η x0 xi ξ t)

theorem actualMarkedChart_nonzero {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    actualCoordinateFunctions hτ hτone η (actualMarkedChart hτ hτone η x0 xi ξ t)
      (coverTuple τ x0 xi ξ t : ℂ) ≠ 0 :=
  Classical.choose_spec (exists_actualMarkedChart hτ hτone η x0 xi ξ t)

theorem actualNormalizedPoint_coordinates {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) (c : Fin 3) :
    planeCoordinate (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η) c
      (coverTuple τ x0 xi ξ t : ℂ)) =
      chartCoordinates₂ c (actualMarkedPoint hτ hτone η x0 xi ξ t) := by
  funext a
  rw [actualMarkedPoint_eq_mk]
  change (if a = 0 then _ else _) =
    chartCoordinates c (Projectivization.mk ℂ _ _) (chartIndexEquiv c a)
  rw [chartCoordinates_mk]
  fin_cases a <;> rfl

/-- The normalized point has precisely the actual projective image; any valid
chart may be used, including a chart chosen later for a nonzero normal derivative. -/
theorem actualNormalizedPoint_eq {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) (c : Fin 3)
    (hc : actualCoordinateFunctions hτ hτone η c (coverTuple τ x0 xi ξ t : ℂ) ≠ 0) :
    chartPoint₂ c (planeCoordinate (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η) c
      (coverTuple τ x0 xi ξ t : ℂ))) = actualMarkedPoint hτ hτone η x0 xi ξ t := by
  rw [actualNormalizedPoint_coordinates]
  apply chartPoint₂_chartCoordinates₂
  rw [actualMarkedPoint_eq_mk]
  exact (mk_rep_coordinate_ne_zero_iff _ _ c).mpr hc

theorem actualNormalizedConfiguration_injective {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ t, actualCoordinateFunctions hτ hτone η (chart t) (coverTuple τ x0 xi ξ t : ℂ) ≠ 0) :
    Function.Injective (fun t => chartPoint₂ (chart t)
      (planeCoordinate (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η) (chart t)
        (coverTuple τ x0 xi ξ t : ℂ)))) := by
  simpa only [actualNormalizedPoint_eq hτ hτone η x0 xi ξ _ _ (hc _)] using
    actualMarkedPoint_injective hτ hτone η x0 xi ξ hinj

end Nagata.W06.TorusConfiguration

end
end

section

/-! Exact all-r source configurations using the actual cubic map and unchanged
zero/Pi multiplier displacements. No geometric embedding input remains. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W07 Nagata.W21 Nagata.ProjectiveGeometry
open Nagata.Workers.W17 Nagata.Workers.W28

/-- Exact covering lifts after the source equality r=9+q. -/
def actualCoverOfEq {r q : ℕ} (hr : r = 9 + q) (τ x0 : ℝ)
    (xi : Fin 9 → ℝ) (ξ : Fin q → ℂ) (i : Fin r) : ℂˣ :=
  coverTuple τ x0 xi ξ (Fin.cast hr i)

/-- The literal source displacement over each reindexed genuine torus point.
This is an actual multiplier fibre, whose geometric normal identification is separate. -/
def actualDisplacementOfEq {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (η x0 : ℝ) (xi : Fin 9 → ℝ) (ξ : Fin q → ℂ) (i : Fin r) :
    QuotientFibre (positivePeriod τ hτ) (rayPoint τ η ^ 3) 9
      (torusPointMk (positivePeriod τ hτ) (actualCoverOfEq hr τ x0 xi ξ i)) :=
  normalDisplacement τ hτ (rayPoint τ η) x0 xi ξ (Fin.cast hr i)

/-- Full list compatibility with the genuine global Pi map, with the cubic's
actual degree-three multiplier τ^η; this holds for every indexed point. -/
theorem actualDisplacementOfEq_globalPi {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η x0 : ℝ) (xi : Fin 9 → ℝ)
    (ξ : Fin q → ℂ) (i : Fin r) :
    (actualDisplacementOfEq hr hτ η x0 xi ξ i).val =
      piQuotientMap hτ hτone (rayPoint τ η) xi
        (Quotient.mk _ (actualCoverOfEq hr τ x0 xi ξ i, (1 : ℂ))) :=
  normalDisplacement_eq_globalPi hτ hτone (rayPoint τ η) x0 xi ξ (Fin.cast hr i)

theorem actualNormalizedConfigurationOfEq_injective {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η x0 : ℝ) (xi : Fin 9 → ℝ)
    (ξ : Fin q → ℂ) (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (chart : Fin r → Fin 3)
    (hc : ∀ i, actualCoordinateFunctions hτ hτone η (chart i)
      (actualCoverOfEq hr τ x0 xi ξ i : ℂ) ≠ 0) :
    Function.Injective (fun i => chartPoint₂ (chart i)
      (planeCoordinate (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η) (chart i)
        (actualCoverOfEq hr τ x0 xi ξ i : ℂ)))) := by
  intro i j hij
  apply (Fin.cast_injective hr)
  apply actualMarkedPoint_injective hτ hτone η x0 xi ξ hinj
  exact (actualNormalizedPoint_eq hτ hτone η x0 xi ξ (Fin.cast hr i) (chart i) (hc i)).symm.trans
    (hij.trans (actualNormalizedPoint_eq hτ hτone η x0 xi ξ (Fin.cast hr j) (chart j) (hc j)))

/-- The actual source configuration exists for every period and every r≥9,
with q=r−9, for every distinct tuple in a common disk. The source's literal
eta and all homogeneous representatives are retained. -/
theorem actual_source_configuration_for_every_period {Δ τ : ℝ}
    (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2) (hτ : 0 < τ) (hτone : τ < 1) (rhoStar : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (r : ℕ) (hr : 9 ≤ r) (ξ : Fin (r - 9) → ℂ),
      Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
      ∃ p : OrderedDistinctPoints r,
        (∀ i : Fin r, p.val i =
          actualMarkedPoint hτ hτone (((∑ j, markedExponent Δ j) + rhoStar) / 3)
            (1 / 2) (markedExponent Δ) ξ (Fin.cast (by omega : r = 9 + (r - 9)) i)) ∧
        (∀ j, markedPi τ (markedExponent Δ) (chartPoint τ (1 / 2) (ξ j) : ℂ) ≠ 0) := by
  obtain ⟨R, hR, hcfg⟩ := sourceMarkedAssembly_for_every_period hΔ hhalf hτ hτone
  refine ⟨R, hR, ?_⟩
  intro r hr ξ hξ hξR
  obtain ⟨hinj, hPi⟩ := hcfg (r - 9) ξ hξ hξR
  exact ⟨actualMarkedConfigurationOfEq (by omega) hτ hτone
    (((∑ j, markedExponent Δ j) + rhoStar) / 3) (1 / 2) (markedExponent Δ) ξ hinj,
    fun _ => rfl, hPi⟩

end Nagata.W06.TorusConfiguration

end
end

section

noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- The chosen containing chart has a genuine nonzero polynomial differential. -/
theorem actualMarkedChart_gradient {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (hzero : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval
      (fun i => actualCoordinateFunctions hτ hτone η i z) G = 0)
    (hgrad : ∀ z : ℂ, z ≠ 0 → ∃ j, MvPolynomial.eval
      (fun i => actualCoordinateFunctions hτ hτone η i z) (MvPolynomial.pderiv j G) ≠ 0)
    (t : Fin (9 + q)) :
    polynomialGradient (Nagata.W27.directChartHom (actualMarkedChart hτ hτone η x0 xi ξ t) G)
      (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η)
        (actualMarkedChart hτ hτone η x0 xi ξ t) (coverTuple τ x0 xi ξ t : ℂ)) ≠ 0 :=
  Nagata.Workers.W25.normalizedCurvePoint_gradient_ne_zero hG
    (actualMarkedChart hτ hτone η x0 xi ξ t) (actualCoordinateFunctions hτ hτone η)
    (coverTuple τ x0 xi ξ t : ℂ) (actualMarkedChart_nonzero hτ hτone η x0 xi ξ t)
    (hzero _ (coverTuple τ x0 xi ξ t).ne_zero)
    (hgrad _ (coverTuple τ x0 xi ξ t).ne_zero)

/-- The exact simultaneous chart package for actual normal specialization:
nonzero denominator, distinct projective base points, nonzero actual differential. -/
theorem actualMarked_smooth_chart_data {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (hzero : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval
      (fun i => actualCoordinateFunctions hτ hτone η i z) G = 0)
    (hgrad : ∀ z : ℂ, z ≠ 0 → ∃ j, MvPolynomial.eval
      (fun i => actualCoordinateFunctions hτ hτone η i z) (MvPolynomial.pderiv j G) ≠ 0) :
    (∀ t, actualCoordinateFunctions hτ hτone η (actualMarkedChart hτ hτone η x0 xi ξ t)
      (coverTuple τ x0 xi ξ t : ℂ) ≠ 0) ∧
    Function.Injective (fun t => chartPoint₂ (actualMarkedChart hτ hτone η x0 xi ξ t)
      (planeCoordinate (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η)
        (actualMarkedChart hτ hτone η x0 xi ξ t) (coverTuple τ x0 xi ξ t : ℂ)))) ∧
    (∀ t, polynomialGradient
      (Nagata.W27.directChartHom (actualMarkedChart hτ hτone η x0 xi ξ t) G)
      (normalizedCurvePoint (actualCoordinateFunctions hτ hτone η)
        (actualMarkedChart hτ hτone η x0 xi ξ t) (coverTuple τ x0 xi ξ t : ℂ)) ≠ 0) := by
  refine ⟨actualMarkedChart_nonzero hτ hτone η x0 xi ξ, ?_, ?_⟩
  · exact actualNormalizedConfiguration_injective hτ hτone η x0 xi ξ hinj
      (actualMarkedChart hτ hτone η x0 xi ξ) (actualMarkedChart_nonzero hτ hτone η x0 xi ξ)
  · exact actualMarkedChart_gradient hτ hτone η x0 xi ξ G hG hzero hgrad

end Nagata.W06.TorusConfiguration

end
end

section

noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.Workers.W10 Nagata.W08 Nagata.CoefficientSpaces
open scoped BigOperators

/-- Actual coordinate sections, with the source's unreduced τ^η multiplier type. -/
def sourceCoordinateSections {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) :
    Fin 3 → automorphicSections (τ : ℂ) 3 (tauPower τ (((∑ i, marks i) + a) / 3)) :=
  fun i => ⟨(actualCoordinateSections hτ hτone (((∑ i, marks i) + a) / 3) i).val,
    by simpa only [rayPoint_eq_real_rpow hτ, tauPower] using
      (actualCoordinateSections hτ hτone (((∑ i, marks i) + a) / 3) i).property⟩

@[simp] theorem sourceCoordinateSections_val {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) (i : Fin 3) :
    (sourceCoordinateSections hτ hτone marks a i).val =
      actualCoordinateFunctions hτ hτone (((∑ j, marks j) + a) / 3) i := rfl

/-- Both finite indexing conventions list exactly the same nonzero covering lifts. -/
theorem markedNormalBase_eq_coverTuple {τ : ℝ} (hτ : 0 < τ)
    (marks : Fin 9 → ℝ) (x0 : ℝ) {q : ℕ} (ξ : Fin q → ℂ) (b : Fin (9 + q)) :
    markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
      (logarithmicPoints (tauPower τ x0) ξ) b = (coverTuple τ x0 marks ξ b : ℂ) := by
  refine Fin.addCases ?_ ?_ b
  · intro i
    have he := coverTuple_left τ x0 marks ξ i
    rw [finSumFinEquiv_apply_left] at he
    rw [he]
    simp only [markedNormalBase, Fin.addCases_left, rayPoint_eq_real_rpow hτ]
  · intro j
    have he := coverTuple_right τ x0 marks ξ j
    rw [finSumFinEquiv_apply_right] at he
    rw [he]
    simp only [markedNormalBase, Fin.addCases_right, logarithmicPoints,
      chartPoint_eq_real_rpow hτ, tauPower]

/-- Pointwise equality extends to the complete actual finite base list. -/
theorem markedNormalBase_eq_coverTuple_fun {τ : ℝ} (hτ : 0 < τ)
    (marks : Fin 9 → ℝ) (x0 : ℝ) {q : ℕ} (ξ : Fin q → ℂ) :
    markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ)) (logarithmicPoints (tauPower τ x0) ξ) =
      fun b => (coverTuple τ x0 marks ξ b : ℂ) :=
  funext (markedNormalBase_eq_coverTuple hτ marks x0 ξ)

end Nagata.W06.TorusConfiguration

end
end

section

noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.Workers.W10 Nagata.Workers.W17 Nagata.Workers.W28
open Nagata.W07 Nagata.W21 Nagata.ProjectiveGeometry Nagata.CoefficientSpaces
open scoped BigOperators

/-- One actual regular cubic and actual source-typed coordinate space supply all
marked configurations. Distinctness is the only tuple condition; the fixed-period
disk theorem proves it for every distinct tuple sufficiently near zero. -/
theorem exists_actual_source_smooth_geometry {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) :
    ∃ C : MvPolynomial (Fin 3) ℂ, Prime C ∧ C.IsHomogeneous 3 ∧
      ∃ X : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3
          (tauPower τ (((∑ i, marks i) + a) / 3)),
        Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) = Ideal.span ({C} : Set _) ∧
        ∀ (q : ℕ) (ξ : Fin q → ℂ),
          Function.Injective (torusTuple τ hτ (1 / 2) marks ξ) →
          ∃ chart : Fin (9 + q) → Fin 3,
            (∀ b, (X (chart b)).val
              (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
                (logarithmicPoints (tauPower τ (1 / 2)) ξ) b) ≠ 0) ∧
            Function.Injective (fun b => chartPoint₂ (chart b)
              (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
                (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
                  (logarithmicPoints (tauPower τ (1 / 2)) ξ) b)))) ∧
            (∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) C)
              (normalizedCurvePoint (fun i => (X i).val) (chart b)
                (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
                  (logarithmicPoints (tauPower τ (1 / 2)) ξ) b)) ≠ 0) := by
  let η : ℝ := ((∑ i, marks i) + a) / 3
  obtain ⟨C, hCprime, hChom, hCdegree, hrel, hzero, hgrad, hnoncancel⟩ :=
    exists_actual_regular_prime_cubic hτ hτone (rayPoint τ η).ne_zero
  refine ⟨C, hCprime, hChom, sourceCoordinateSections hτ hτone marks a, ?_, ?_⟩
  · exact hrel
  · intro q ξ hinj
    refine ⟨actualMarkedChart hτ hτone η (1 / 2) marks ξ, ?_⟩
    have hdata := actualMarked_smooth_chart_data hτ hτone η (1 / 2) marks ξ hinj C hChom hzero hgrad
    simpa only [sourceCoordinateSections_val, markedNormalBase_eq_coverTuple hτ,
      η] using hdata

end Nagata.W06.TorusConfiguration

end
end

end OAI
