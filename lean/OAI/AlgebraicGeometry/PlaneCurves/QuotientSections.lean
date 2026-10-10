import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Group.Units
import OAI.AlgebraicGeometry.PlaneCurves.Multipliers
import OAI.AlgebraicGeometry.PlaneCurves.Parameters

namespace OAI

/-!
# Sections on the torus quotient and holomorphic chart equivalences; Holomorphic division producing quotient sections; Finite lists of quotient sections and their fibre values
-/

section

/-! The open-domain equivalence between holomorphic and analytic section functions. -/
namespace Nagata.W08

/-- Every concrete multiplier section is complex analytic at every genuine point. -/
theorem automorphicSection_analyticAt {τ γ : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ f.val z := by
  have hd : DifferentiableOn ℂ f.val {w : ℂ | w ≠ 0} :=
    fun w hw ↦ (f.property.2.1 w hw).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hz)

/-- Analyticity on a neighborhood of each point of the punctured plane. -/
theorem automorphicSection_analyticOnNhd {τ γ : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) :
    AnalyticOnNhd ℂ f.val {z : ℂ | z ≠ 0} :=
  fun _ hz ↦ automorphicSection_analyticAt f hz

end Nagata.W08

end

section

noncomputable section
namespace Nagata.W08

open Nagata.W21

variable {R : Type*} [CommGroupWithZero R]

/-- Scalar functions with the literal one-step multiplier law on the genuine cover. -/
def EquivariantFunctions (τ γ : Rˣ) (n : ℤ) :=
  {f : Rˣ → R // ∀ z, f (τ * z) = (↑(γ * z ^ (-n)) : R) * f z}

/-- Actual right-inverse sections of the projection of the actual orbit quotient. -/
def QuotientSections (τ γ : Rˣ) (n : ℤ) :=
  {s : TorusPoint τ → MultiplierQuotient τ γ n //
    ∀ q, multiplierQuotientProjection τ γ n (s q) = q}

/-- Equivariance under one generator propagates to every integer deck transformation. -/
theorem multiplierIterate_graph (τ γ : Rˣ) (n : ℤ)
    (f : EquivariantFunctions τ γ n) (k : ℤ) (z : Rˣ) :
    multiplierIterate τ γ n k (z, f.val z) = (τ ^ k * z, f.val (τ ^ k * z)) := by
  have hseq : (fun k : ℤ ↦ multiplierIterate τ γ n k (z, f.val z)) =
      (fun k : ℤ ↦ (τ ^ k * z, f.val (τ ^ k * z))) := by
    apply biInfinite_unique (fun _ p ↦ multiplierStep τ γ n p)
    · intro _ p q hpq
      exact (multiplierStep τ γ n).injective hpq
    · intro k
      rw [show k + 1 = 1 + k by omega, multiplierIterate_add]
      simp only [multiplierIterate, zpow_one]
    · intro k
      have hbase : τ ^ (k + 1) * z = τ * (τ ^ k * z) := by
        rw [zpow_add_one]
        ac_rfl
      change (τ ^ (k + 1) * z, f.val (τ ^ (k + 1) * z)) =
        (τ * (τ ^ k * z), (↑(γ * (τ ^ k * z) ^ (-n)) : R) * f.val (τ ^ k * z))
      rw [hbase, f.property]
    · simp
  exact congrFun hseq k

/-- An equivariant scalar function descends to an actual quotient section. -/
def quotientSectionOfEquivariant (τ γ : Rˣ) (n : ℤ)
    (f : EquivariantFunctions τ γ n) : QuotientSections τ γ n :=
  ⟨Quotient.lift (fun z : Rˣ ↦ (Quotient.mk _ (z, f.val z) : MultiplierQuotient τ γ n))
    (by
      intro z w hzw
      obtain ⟨k, hk⟩ := hzw
      apply Quotient.sound
      refine ⟨k, ?_⟩
      rw [multiplierIterate_graph, hk]), by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    rfl⟩

@[simp] theorem quotientSectionOfEquivariant_apply (τ γ : Rˣ) (n : ℤ)
    (f : EquivariantFunctions τ γ n) (z : Rˣ) :
    (quotientSectionOfEquivariant τ γ n f).val (torusPointMk τ z) =
      (Quotient.mk _ (z, f.val z) : MultiplierQuotient τ γ n) := rfl

/-- Every quotient fibre point has a scalar representative over each chosen lift of its base. -/
theorem quotient_fibre_representative (τ γ : Rˣ) (n : ℤ)
    (q : MultiplierQuotient τ γ n) (z : Rˣ)
    (hq : multiplierQuotientProjection τ γ n q = torusPointMk τ z) :
    ∃ t : R, (Quotient.mk _ (z, t) : MultiplierQuotient τ γ n) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, hk⟩ := (torusPointMk_eq_iff τ p.1 z).mp hq
    refine ⟨(multiplierIterate τ γ n k p).2, ?_⟩
    have hp : (z, (multiplierIterate τ γ n k p).2) = multiplierIterate τ γ n k p := by
      apply Prod.ext
      · exact (multiplierIterate_base τ γ n k p).trans hk |>.symm
      · rfl
    rw [hp]
    exact (Quotient.sound (s := multiplierOrbitSetoid τ γ n) ⟨k, rfl⟩).symm

/-- Freeness ensures that the scalar coordinate over a fixed lift is unique. -/
theorem quotient_fibre_coordinate_injective (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : Rˣ) :
    Function.Injective (fun t : R ↦ (Quotient.mk _ (z, t) : MultiplierQuotient τ γ n)) := by
  intro t u htu
  obtain ⟨k, hk⟩ := Quotient.exact htu
  have hbase := congrArg Prod.fst hk
  rw [multiplierIterate_base] at hbase
  have hpow : τ ^ k = 1 := mul_right_cancel (hbase.trans (one_mul z).symm)
  have hkzero := hfree k hpow
  subst k
  simpa only [multiplierIterate_zero, Prod.mk.injEq, true_and] using hk

/-- Extract the unique scalar over a chosen lift from an actual quotient section. -/
def quotientSectionScalar (τ γ : Rˣ) (n : ℤ)
    (s : QuotientSections τ γ n) (z : Rˣ) : R :=
  Classical.choose (quotient_fibre_representative τ γ n
    (s.val (torusPointMk τ z)) z (s.property _))

@[simp] theorem quotientSectionScalar_represents (τ γ : Rˣ) (n : ℤ)
    (s : QuotientSections τ γ n) (z : Rˣ) :
    (Quotient.mk _ (z, quotientSectionScalar τ γ n s z) : MultiplierQuotient τ γ n) =
      s.val (torusPointMk τ z) :=
  Classical.choose_spec (quotient_fibre_representative τ γ n
    (s.val (torusPointMk τ z)) z (s.property _))

/-- One generator identifies exactly the source multiplier-related representatives. -/
theorem quotient_mk_multiplierStep (τ γ : Rˣ) (n : ℤ) (z : Rˣ) (t : R) :
    (Quotient.mk _ (τ * z, (↑(γ * z ^ (-n)) : R) * t) : MultiplierQuotient τ γ n) =
      Quotient.mk _ (z, t) := by
  apply Eq.symm
  apply Quotient.sound
  refine ⟨1, ?_⟩
  simp only [multiplierIterate, zpow_one]
  rfl

/-- The scalar extracted from an actual quotient section is genuinely equivariant. -/
theorem quotientSectionScalar_equivariant (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (s : QuotientSections τ γ n) (z : Rˣ) :
    quotientSectionScalar τ γ n s (τ * z) =
      (↑(γ * z ^ (-n)) : R) * quotientSectionScalar τ γ n s z := by
  apply quotient_fibre_coordinate_injective τ γ n hfree (τ * z)
  dsimp only
  rw [quotientSectionScalar_represents, quotient_mk_multiplierStep,
    quotientSectionScalar_represents]
  exact congrArg s.val ((torusPointMk_eq_iff τ z (τ * z)).mpr ⟨1, by simp⟩).symm

/-- Extract an equivariant function from an actual quotient section. -/
def equivariantOfQuotientSection (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (s : QuotientSections τ γ n) : EquivariantFunctions τ γ n :=
  ⟨quotientSectionScalar τ γ n s, quotientSectionScalar_equivariant τ γ n hfree s⟩

/-- Extracting after descending returns every original scalar value. -/
theorem equivariantOfQuotientSection_left_inverse (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (f : EquivariantFunctions τ γ n) :
    equivariantOfQuotientSection τ γ n hfree (quotientSectionOfEquivariant τ γ n f) = f := by
  apply Subtype.ext
  funext z
  apply quotient_fibre_coordinate_injective τ γ n hfree z
  exact quotientSectionScalar_represents τ γ n (quotientSectionOfEquivariant τ γ n f) z

/-- Descending after extracting returns the actual original quotient section. -/
theorem quotientSectionOfEquivariant_right_inverse (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (s : QuotientSections τ γ n) :
    quotientSectionOfEquivariant τ γ n (equivariantOfQuotientSection τ γ n hfree s) = s := by
  apply Subtype.ext
  funext q
  refine Quotient.inductionOn q ?_
  intro z
  exact quotientSectionScalar_represents τ γ n s z

/-- The actual algebraic section/function equivalence of the actual quotient projection.
Holomorphic compatibility is not asserted by this set-level equivalence. -/
def equivariantQuotientSectionEquiv (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) :
    EquivariantFunctions τ γ n ≃ QuotientSections τ γ n where
  toFun := quotientSectionOfEquivariant τ γ n
  invFun := equivariantOfQuotientSection τ γ n hfree
  left_inv := equivariantOfQuotientSection_left_inverse τ γ n hfree
  right_inv := quotientSectionOfEquivariant_right_inverse τ γ n hfree

end Nagata.W08

end
end

section

/-! Actual quotient fibres and fixed-lift scalar coordinates for finite displacement lists.
No abstract bundle or normal-identification axiom is introduced. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.W21

/-- An actual fibre of the multiplier-orbit quotient projection. -/
abbrev QuotientFibre (τ γ : ℂˣ) (n : ℤ) (p : TorusPoint τ) :=
  {w : MultiplierQuotient τ γ n // multiplierQuotientProjection τ γ n w = p}

/-- The vector with scalar c over the chosen nonzero lift z. -/
def fibreRepresentative (τ γ : ℂˣ) (n : ℤ) (z : ℂˣ) (c : ℂ) :
    QuotientFibre τ γ n (torusPointMk τ z) :=
  ⟨Quotient.mk _ (z, c), rfl⟩

theorem fibreRepresentative_injective (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) :
    Function.Injective (fibreRepresentative τ γ n z) := by
  intro a b h
  exact Nagata.W08.quotient_fibre_coordinate_injective τ γ n hfree z (congrArg Subtype.val h)

theorem fibreRepresentative_surjective (τ γ : ℂˣ) (n : ℤ) (z : ℂˣ) :
    Function.Surjective (fibreRepresentative τ γ n z) := by
  intro w
  obtain ⟨c, hc⟩ := Nagata.W08.quotient_fibre_representative τ γ n w.val z w.property
  exact ⟨c, Subtype.ext hc⟩

/-- A proved coordinate bijection for the actual quotient fibre over a fixed lift. -/
def fibreCoordinateEquiv (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) :
    ℂ ≃ QuotientFibre τ γ n (torusPointMk τ z) :=
  Equiv.ofBijective (fibreRepresentative τ γ n z)
    ⟨fibreRepresentative_injective τ γ n hfree z, fibreRepresentative_surjective τ γ n z⟩

@[simp] theorem fibreCoordinateEquiv_apply (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) (c : ℂ) :
    fibreCoordinateEquiv τ γ n hfree z c = fibreRepresentative τ γ n z c := rfl

/-- Scalar multiplication between the actual two fibres in the specified covering frames.
This finite-fibre map does not assert that these maps glue into a global bundle morphism. -/
def fibreScaleAtLift (τ γA γM : ℂˣ) (nA nM : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) (P : ℂ) :
    QuotientFibre τ γA nA (torusPointMk τ z) → QuotientFibre τ γM nM (torusPointMk τ z) :=
  fun w => fibreCoordinateEquiv τ γM nM hfree z
    (P * (fibreCoordinateEquiv τ γA nA hfree z).symm w)

theorem fibreScaleAtLift_representative (τ γA γM : ℂˣ) (nA nM : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) (P c : ℂ) :
    fibreScaleAtLift τ γA γM nA nM hfree z P (fibreRepresentative τ γA nA z c) =
      fibreRepresentative τ γM nM z (P * c) := by
  change fibreCoordinateEquiv τ γM nM hfree z
    (P * (fibreCoordinateEquiv τ γA nA hfree z).symm
      (fibreCoordinateEquiv τ γA nA hfree z c)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The source scalar-one vector is sent to the target scalar-P vector. -/
theorem fibreScaleAtLift_one (τ γA γM : ℂˣ) (nA nM : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) (P : ℂ) :
    fibreScaleAtLift τ γA γM nA nM hfree z P (fibreRepresentative τ γA nA z 1) =
      fibreRepresentative τ γM nM z P := by
  rw [fibreScaleAtLift_representative, mul_one]

theorem fibreRepresentative_ne_zero (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (z : ℂˣ) (c : ℂ) (hc : c ≠ 0) :
    fibreRepresentative τ γ n z c ≠ fibreRepresentative τ γ n z 0 := by
  intro h
  exact hc (fibreRepresentative_injective τ γ n hfree z h)

end Nagata.W06.TorusConfiguration

end
end

section

/-!
Descent of genuine holomorphic multiplier functions to actual sections of the
actual quotient projection. Compatibility with a holomorphic local-trivialization
atlas is separate from the checked set-level descent and inverse below.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W21

/-- Restriction of the actual holomorphic section to its genuine unit-valued cover. -/
def automorphicToEquivariant (τ γ : ℂˣ) (n : ℤ)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) : EquivariantFunctions τ γ n :=
  ⟨fun z ↦ f.val (z : ℂ), fun z ↦ by
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using
      f.property.2.2 (z : ℂ) (Units.ne_zero z)⟩

/-- Restriction loses no actual holomorphic sections. -/
theorem automorphicToEquivariant_injective (τ γ : ℂˣ) (n : ℤ) :
    Function.Injective (automorphicToEquivariant τ γ n) := by
  intro f g hfg
  apply automorphicSections_ext
  intro z hz
  exact congrFun (congrArg Subtype.val hfg) (Units.mk0 z hz)

/-- An actual holomorphic multiplier function yields an actual right-inverse section. -/
def quotientSectionOfAutomorphic (τ γ : ℂˣ) (n : ℤ)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) : QuotientSections τ γ n :=
  quotientSectionOfEquivariant τ γ n (automorphicToEquivariant τ γ n f)

/-- The quotient representative uses exactly the function's covering-frame scalar. -/
@[simp] theorem quotientSectionOfAutomorphic_apply (τ γ : ℂˣ) (n : ℤ)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) (z : ℂˣ) :
    (quotientSectionOfAutomorphic τ γ n f).val (torusPointMk τ z) =
      (Quotient.mk _ (z, f.val (z : ℂ)) : MultiplierQuotient τ γ n) := rfl

/-- Scalar extraction from the descended actual quotient section recovers the original value. -/
theorem quotientSectionOfAutomorphic_scalar (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) (f : automorphicSections (τ : ℂ) n (γ : ℂ)) (z : ℂˣ) :
    quotientSectionScalar τ γ n (quotientSectionOfAutomorphic τ γ n f) z = f.val (z : ℂ) := by
  apply quotient_fibre_coordinate_injective τ γ n (unitPeriod_free τ hτ) z
  exact quotientSectionScalar_represents τ γ n (quotientSectionOfAutomorphic τ γ n f) z

/-- Distinct holomorphic covering functions give distinct actual quotient sections. -/
theorem quotientSectionOfAutomorphic_injective (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) : Function.Injective (quotientSectionOfAutomorphic τ γ n) := by
  intro f g hfg
  apply automorphicSections_ext
  intro z hz
  have h := congrArg (fun s ↦ quotientSectionScalar τ γ n s (Units.mk0 z hz)) hfg
  simpa only [quotientSectionOfAutomorphic_scalar τ γ n hτ, Units.val_mk0] using h

end Nagata.W08

end
end

section

/-!
The checked scalar-function descent agrees with the actual quotient local
homeomorphism charts. Holomorphy is verified in these actual fibre coordinates.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W21 Filter Topology

/-- The actual fibre chart recovers the unique scalar of an arbitrary quotient section. -/
theorem quotientSection_fibreChart (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (U : Set ℂˣ) (hU : IsOpen U) (hinj : Set.InjOn (torusPointMk τ) U)
    (s : QuotientSections τ γ n) {z : ℂˣ} (hz : z ∈ U) :
    (multiplierFibreChart τ γ n hfree U hU hinj).symm (s.val (torusPointMk τ z)) =
      (z, quotientSectionScalar τ γ n s z) := by
  rw [← quotientSectionScalar_represents τ γ n s z]
  exact (multiplierFibreChart τ γ n hfree U hU hinj).left_inv ⟨hz, Set.mem_univ _⟩

/-- The scalar local coordinate of a quotient section, expressed in the genuine complex base
coordinate. Outside the chart domain its values have no geometric meaning. -/
def quotientChartScalar (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (U : Set ℂˣ) (hU : IsOpen U) (hinj : Set.InjOn (torusPointMk τ) U)
    (s : QuotientSections τ γ n) (w : ℂ) : ℂ :=
  if hw : w = 0 then 0 else
    ((multiplierFibreChart τ γ n hfree U hU hinj).symm
      (s.val (torusPointMk τ (Units.mk0 w hw)))).2

/-- Exact local-coordinate formula for every actual section. -/
theorem quotientChartScalar_eq (τ γ : ℂˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0)
    (U : Set ℂˣ) (hU : IsOpen U) (hinj : Set.InjOn (torusPointMk τ) U)
    (s : QuotientSections τ γ n) {z : ℂˣ} (hz : z ∈ U) :
    quotientChartScalar τ γ n hfree U hU hinj s (z : ℂ) =
      quotientSectionScalar τ γ n s z := by
  have hmk : Units.mk0 (z : ℂ) (Units.ne_zero z) = z := Units.ext rfl
  simp only [quotientChartScalar, dite_eq_right (Units.ne_zero z)]
  rw [hmk, quotientSection_fibreChart τ γ n hfree U hU hinj s hz]

/-- The actual quotient fibre-coordinate function equals the original holomorphic scalar. -/
theorem quotientChartScalar_automorphic_eq (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1)
    (U : Set ℂˣ) (hU : IsOpen U) (hinj : Set.InjOn (torusPointMk τ) U)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) {z : ℂˣ} (hz : z ∈ U) :
    quotientChartScalar τ γ n (unitPeriod_free τ hτ) U hU hinj
      (quotientSectionOfAutomorphic τ γ n f) (z : ℂ) = f.val (z : ℂ) := by
  rw [quotientChartScalar_eq τ γ n (unitPeriod_free τ hτ) U hU hinj _ hz,
    quotientSectionOfAutomorphic_scalar τ γ n hτ]

/-- The descended actual section is holomorphic in every actual fibre chart. -/
theorem quotientChartScalar_automorphic_differentiableAt (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1)
    (U : Set ℂˣ) (hU : IsOpen U) (hinj : Set.InjOn (torusPointMk τ) U)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) {z : ℂˣ} (hz : z ∈ U) :
    DifferentiableAt ℂ (quotientChartScalar τ γ n (unitPeriod_free τ hτ) U hU hinj
      (quotientSectionOfAutomorphic τ γ n f)) (z : ℂ) := by
  apply (f.property.2.1 (z : ℂ) (Units.ne_zero z)).congr_of_eventuallyEq
  have hmem : (fun u : ℂˣ ↦ (u : ℂ)) '' U ∈ 𝓝 (z : ℂ) :=
    (Units.isOpenMap_val U hU).mem_nhds ⟨z, hz, rfl⟩
  filter_upwards [hmem] with w hw
  obtain ⟨u, hu, rfl⟩ := hw
  exact quotientChartScalar_automorphic_eq τ γ n hτ U hU hinj f hu

end Nagata.W08

end
end

section

namespace Nagata.CoefficientSpaces

/-- Quotient construction directly from genuine holomorphic multiplier sections:
analyticity is derived, with no additional analyticity hypotheses. -/
theorem exists_holomorphic_quotient {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ)
    (P : Nagata.W08.automorphicSections τ s δ) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.automorphicSections τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z :=
  exists_automorphic_quotient hτ hδ f P
    (Nagata.W08.automorphicSection_analyticOnNhd f)
    (Nagata.W08.automorphicSection_analyticOnNhd P) k hzero

/-- The actual low coefficient extension without redundant analytic assumptions. -/
theorem exists_low_holomorphic_coefficient {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0)
    (d m j : ℤ) (hj : j ≤ m)
    (P : Nagata.W08.automorphicSections τ 9 Q)
    (f : Nagata.W08.automorphicSections τ (3 * (d - 3 * j)) (L ^ (d - 3 * j)))
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j).toNat : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ coefficientSpace τ L Q d m j P.val,
      ∀ z ≠ 0, f.val z = P.val z ^ (m - j).toNat * g z :=
  exists_low_coefficient hτ hL hQ d m j hj P f
    (Nagata.W08.automorphicSection_analyticOnNhd P)
    (Nagata.W08.automorphicSection_analyticOnNhd f) hzero

end Nagata.CoefficientSpaces

end

section

/-!
Holomorphy of actual quotient sections, defined by their actual local fibre
coordinates. The correspondence with holomorphic covering functions is proved
in both directions. Existence of an injective open base slice at every point
is an explicit prerequisite for the forward equivalence, not an assumed
conclusion in the section type.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W21 Filter Topology

/-- Standard local-coordinate holomorphy for an actual section of the quotient projection. -/
def IsChartHolomorphic (τ γ : ℂˣ) (n : ℤ) (hτ : ‖(τ : ℂ)‖ < 1)
    (s : QuotientSections τ γ n) : Prop :=
  ∀ z : ℂˣ, ∃ U : Set ℂˣ, ∃ hU : IsOpen U, ∃ hinj : Set.InjOn (torusPointMk τ) U,
    z ∈ U ∧ DifferentiableAt ℂ
      (quotientChartScalar τ γ n (unitPeriod_free τ hτ) U hU hinj s) (z : ℂ)

/-- The unique scalar extracted from an actual section, represented by a zero extension. -/
def quotientSectionZeroScalar (τ γ : ℂˣ) (n : ℤ) (s : QuotientSections τ γ n) (w : ℂ) : ℂ :=
  if hw : w = 0 then 0 else quotientSectionScalar τ γ n s (Units.mk0 w hw)

@[simp] theorem quotientSectionZeroScalar_zero (τ γ : ℂˣ) (n : ℤ)
    (s : QuotientSections τ γ n) : quotientSectionZeroScalar τ γ n s 0 = 0 := by
  simp [quotientSectionZeroScalar]

@[simp] theorem quotientSectionZeroScalar_unit (τ γ : ℂˣ) (n : ℤ)
    (s : QuotientSections τ γ n) (z : ℂˣ) :
    quotientSectionZeroScalar τ γ n s (z : ℂ) = quotientSectionScalar τ γ n s z := by
  simp only [quotientSectionZeroScalar, dite_eq_right (Units.ne_zero z)]
  congr 1
  exact Units.ext rfl

/-- Holomorphy in an actual fibre chart implies holomorphy of the extracted covering scalar. -/
theorem quotientSectionZeroScalar_differentiableAt (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) (s : QuotientSections τ γ n)
    (hs : IsChartHolomorphic τ γ n hτ s) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (quotientSectionZeroScalar τ γ n s) w := by
  let z : ℂˣ := Units.mk0 w hw
  obtain ⟨U, hU, hinj, hz, hd⟩ := hs z
  have hmem : (fun u : ℂˣ ↦ (u : ℂ)) '' U ∈ 𝓝 w :=
    (Units.isOpenMap_val U hU).mem_nhds ⟨z, hz, rfl⟩
  apply hd.congr_of_eventuallyEq
  filter_upwards [hmem] with v hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [quotientSectionZeroScalar_unit,
    quotientChartScalar_eq τ γ n (unitPeriod_free τ hτ) U hU hinj s hu]

/-- The extracted scalar satisfies the actual multiplier equation. -/
theorem quotientSectionZeroScalar_automorphy (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) (s : QuotientSections τ γ n) {w : ℂ} (hw : w ≠ 0) :
    quotientSectionZeroScalar τ γ n s ((τ : ℂ) * w) =
      (γ : ℂ) * w ^ (-n) * quotientSectionZeroScalar τ γ n s w := by
  let z : ℂˣ := Units.mk0 w hw
  have he : w = (z : ℂ) := rfl
  rw [he, ← Units.val_mul, quotientSectionZeroScalar_unit, quotientSectionZeroScalar_unit,
    quotientSectionScalar_equivariant τ γ n (unitPeriod_free τ hτ)]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

/-- Extract a genuine holomorphic multiplier function from a chart-holomorphic actual section. -/
def automorphicOfChartHolomorphic (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) (s : QuotientSections τ γ n)
    (hs : IsChartHolomorphic τ γ n hτ s) : automorphicSections (τ : ℂ) n (γ : ℂ) :=
  ⟨quotientSectionZeroScalar τ γ n s, quotientSectionZeroScalar_zero τ γ n s,
    fun _ hw ↦ quotientSectionZeroScalar_differentiableAt τ γ n hτ s hs hw,
    fun _ hw ↦ quotientSectionZeroScalar_automorphy τ γ n hτ s hw⟩

/-- Descent of the extracted holomorphic scalar recovers the actual original section. -/
theorem automorphicOfChartHolomorphic_right_inverse (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1) (s : QuotientSections τ γ n)
    (hs : IsChartHolomorphic τ γ n hτ s) :
    quotientSectionOfAutomorphic τ γ n (automorphicOfChartHolomorphic τ γ n hτ s hs) = s := by
  apply Subtype.ext
  funext q
  refine Quotient.inductionOn q ?_
  intro z
  change (Quotient.mk _ (z, quotientSectionZeroScalar τ γ n s (z : ℂ)) :
    MultiplierQuotient τ γ n) = s.val (torusPointMk τ z)
  rw [quotientSectionZeroScalar_unit, quotientSectionScalar_represents]

/-- When the actual chart slices cover the base, descent is holomorphic everywhere. -/
theorem quotientSectionOfAutomorphic_isChartHolomorphic (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1)
    (hcover : ∀ z : ℂˣ, ∃ U : Set ℂˣ, ∃ _ : IsOpen U,
      ∃ _ : Set.InjOn (torusPointMk τ) U, z ∈ U)
    (f : automorphicSections (τ : ℂ) n (γ : ℂ)) :
    IsChartHolomorphic τ γ n hτ (quotientSectionOfAutomorphic τ γ n f) := by
  intro z
  obtain ⟨U, hU, hinj, hz⟩ := hcover z
  exact ⟨U, hU, hinj, hz, quotientChartScalar_automorphic_differentiableAt τ γ n hτ U hU hinj f hz⟩

def holomorphicQuotientSectionEquiv (τ γ : ℂˣ) (n : ℤ)
    (hτ : ‖(τ : ℂ)‖ < 1)
    (hcover : ∀ z : ℂˣ, ∃ U : Set ℂˣ, ∃ _ : IsOpen U,
      ∃ _ : Set.InjOn (torusPointMk τ) U, z ∈ U) :
    automorphicSections (τ : ℂ) n (γ : ℂ) ≃
      {s : QuotientSections τ γ n // IsChartHolomorphic τ γ n hτ s} where
  toFun f := ⟨quotientSectionOfAutomorphic τ γ n f,
    quotientSectionOfAutomorphic_isChartHolomorphic τ γ n hτ hcover f⟩
  invFun s := automorphicOfChartHolomorphic τ γ n hτ s.val s.property
  left_inv f := by
    apply (quotientSectionOfAutomorphic_injective τ γ n hτ)
    exact automorphicOfChartHolomorphic_right_inverse τ γ n hτ _ _
  right_inv s := by
    apply Subtype.ext
    exact automorphicOfChartHolomorphic_right_inverse τ γ n hτ s.val s.property

end Nagata.W08

end
end

section

/-!
Discharge the chart-cover prerequisite for every actual source period `0<τ<1`.
This yields the unconditional source-period correspondence between genuine
holomorphic multiplier functions and actual chart-holomorphic quotient sections.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W21 Nagata.Workers.W05

/-- The source's actual unit-valued positive period has norm less than one. -/
theorem positivePeriod_norm_lt_one {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ‖((positivePeriod τ hτ : ℂˣ) : ℂ)‖ < 1 := by
  change ‖(τ : ℂ)‖ < 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone

/-- Actual injective open slices cover every source covering-space point. -/
theorem sourcePeriod_chartCover {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ∀ z : ℂˣ, ∃ U : Set ℂˣ, ∃ _ : IsOpen U,
      ∃ _ : Set.InjOn (torusPointMk (positivePeriod τ hτ)) U, z ∈ U := by
  obtain ⟨U, hU, h1, hinj⟩ := exists_injective_identity_slice hτ hτone
  intro z
  obtain ⟨V, hV, hz, hVinj⟩ := exists_open_torus_slice (positivePeriod τ hτ) U hU h1 hinj z
  exact ⟨V, hV, hVinj, hz⟩

def sourceHolomorphicQuotientSectionEquiv {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (γ : ℂˣ) (n : ℤ) :
    automorphicSections (τ : ℂ) n (γ : ℂ) ≃
      {s : QuotientSections (positivePeriod τ hτ) γ n //
        IsChartHolomorphic (positivePeriod τ hτ) γ n (positivePeriod_norm_lt_one hτ hτone) s} :=
  holomorphicQuotientSectionEquiv (positivePeriod τ hτ) γ n
    (positivePeriod_norm_lt_one hτ hτone) (sourcePeriod_chartCover hτ hτone)

end Nagata.W08

end
end

end OAI
