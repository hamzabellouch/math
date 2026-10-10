import OAI.Analysis.Triangular.Main

namespace OAI

/-!
# Gaussian minorants with explicit interpolation coefficients

The atomic construction of the sharp Gaussian minorants gives the two
order-twenty interpolation blocks and an absolutely summable correction.
This formulation records the finite coefficients separately for the two
Hermite basis functions, as in the atomic certificate of OpenAI.
-/

noncomputable section

open scoped BigOperators FourierTransform

namespace AtomicTriangular.Construction

/-- The finite interpolation coefficients with the finite correction added. -/
def correctedFinite (side : Fin 2) (z : ℝ) (δ : Fin 20 → ℝ) (j : Fin 22) : ℝ :=
  (∑ r : Fin 8, Acoefficient side ⟨j.val, by omega⟩ r * actualParameter z r) +
    if hj : j.val < 2 then 0 else δ ⟨j.val - 2, by omega⟩

end AtomicTriangular.Construction

namespace AtomicTriangular

open Construction

local instance finite_pair_neZero : NeZero (2 : ℕ) := inferInstance
local instance three_atLeastTwo : Nat.AtLeastTwo 3 := inferInstance
local instance ten_atLeastTwo : Nat.AtLeastTwo 10 := inferInstance
local instance five_hundred_atLeastTwo : Nat.AtLeastTwo 500 := inferInstance
local instance plane_borelSpace : BorelSpace Plane := inferInstance
local instance plane_finite : Module.Finite ℝ Plane := inferInstance

/-- The two atomic interpolation blocks and their summable correction reconstruct
the minorant with the specified Gaussian normalization. -/
def AtomicConstruction (α : ℝ) (f : Plane → ℝ) : Prop :=
  IsUnit (1 - R) ∧ IsUnit (1 + R) ∧
  (1 - R) * Uplus = Yf + R0 * (gamma 1 + gamma 0) ∧
  (1 + R) * Uminus = Yf + R0 * (gamma 1 - gamma 0) ∧
  ∃ (δ : Fin 2 → Fin 20 → ℝ) (a : Fin 2 → InputCoefficients),
    (∀ side, (∑ j : Fin 20, |δ side j|) < (1 / 10 ^ 5 : ℝ)) ∧
    (∀ side, (a side).C = if side.val = 0 then -(3 / 500) else 3 / 500) ∧
    (∀ side (j : Fin 11),
      (a side).finiteC j =
        correctedFinite side (gaussianZ α) (δ side) ⟨2 * j.val, by omega⟩ ∧
      (a side).finiteD j =
        correctedFinite side (gaussianZ α) (δ side) ⟨2 * j.val + 1, by omega⟩) ∧
    (∀ side, Summable (fun n => |(a side).tailC n| + |(a side).tailD n|) ∧
      (∑' n, (|(a side).tailC n| + |(a side).tailD n|)) < (3 / 10 ^ 9 : ℝ)) ∧
    (∀ x, (f x : ℂ) =
      (inputComplex (a 0) x + 𝓕 (inputComplex (a 1)) x) /
        (normalizingDen (gaussianZ α) : ℂ))

lemma Construction.HasAtomicConstruction.atomicConstruction {α : ℝ} {f : Plane → ℝ}
    (hf : HasAtomicConstruction α f) : AtomicConstruction α f := by
  obtain ⟨hminus, hplus, heqplus, heqminus, a, δ, ha, hδ, hf⟩ := hf
  refine ⟨hminus, hplus, heqplus, heqminus, δ, a,
    (fun side => (hδ side).1), (fun side => (ha side).1), ?_,
    (fun side => (hδ side).2), hf⟩
  intro side j
  constructor
  · have hj := (ha side).2.2.2 ⟨2 * j.val, by omega⟩
    simpa [finiteCoordinates, correctedFinite] using hj
  · have hj := (ha side).2.2.2 ⟨2 * j.val + 1, by omega⟩
    simpa [finiteCoordinates, correctedFinite, Nat.add_div] using hj

/-- Sharp radial Gaussian minorants have nonnegative Fourier transform, exact
lattice contacts, and the atomic construction when the parameter is at least one. -/
theorem sharp_gaussian_minorants_with_construction (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → AtomicConstruction α f) := by
  obtain ⟨f, hradial, hminorant, hfourier, hcontact, hzero, hconstruction⟩ :=
    sharp_gaussian_minorants_atomic α hα
  exact ⟨f, hradial, hminorant, hfourier, hcontact, hzero,
    fun hlarge => (hconstruction hlarge).atomicConstruction⟩

end AtomicTriangular

end

end OAI
