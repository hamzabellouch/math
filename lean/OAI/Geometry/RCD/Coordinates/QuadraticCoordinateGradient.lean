import OAI.Geometry.RCD.Harmonic.HarmonicQuadraticPotential

namespace OAI

/-! # The actual gradient of the quadratic coordinate model -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

private theorem half_square_gamma (u a : SobolevSpace μ hQ) (C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C) :
    localGamma μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u C) a =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ u x * localGamma μ hQ u a x := by
  filter_upwards [localGamma_smul_left μ hQ (1 / 2 : ℝ) (SobolevSpace.square μ hQ u C) a,
    localGamma_square μ hQ u a C hu] with x hsm hsq
  rw [hsm, hsq]
  ring

private theorem finite_half_square_gamma {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (C : ℝ≥0) (a : SobolevSpace μ hQ)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (s : Finset (Fin n)) :
    localGamma μ hQ (∑ j ∈ s, (1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C) a =ᵐ[μ]
      fun x => ∑ j ∈ s, SobolevSpace.toLp μ hQ (u j) x * localGamma μ hQ (u j) a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, zero_smul, zero_mul] using
      localGamma_smul_left μ hQ 0 (0 : SobolevSpace μ hQ) a
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [localGamma_add_left μ hQ
      ((1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C)
      (∑ k ∈ s, (1 / 2 : ℝ) • SobolevSpace.square μ hQ (u k) C) a,
      half_square_gamma μ hQ (u j) a C (hu j), ih] with x hadd hsingle hsum
    rw [hadd, hsingle, hsum]

theorem coordinateQuadratic_gradient {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (C : ℝ≥0) (a : SobolevSpace μ hQ)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C) :
    localGamma μ hQ (coordinateQuadratic μ hQ u C) a =ᵐ[μ]
      fun x => ∑ j, SobolevSpace.toLp μ hQ (u j) x * localGamma μ hQ (u j) a x :=
  finite_half_square_gamma μ hQ u C a hu Finset.univ

/-- The quadratic model has the expected energy density, with the actual
coordinate Gram entries. No Euclidean identity for that Gram is assumed. -/
theorem coordinateQuadratic_gradient_self {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (C : ℝ≥0) (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C) :
    localGamma μ hQ (coordinateQuadratic μ hQ u C) (coordinateQuadratic μ hQ u C) =ᵐ[μ]
      fun x => ∑ i, ∑ j, (SobolevSpace.toLp μ hQ (u i) x * SobolevSpace.toLp μ hQ (u j) x) *
        localGamma μ hQ (u j) (u i) x := by
  have hi (i : Fin n) : localGamma μ hQ (u i) (coordinateQuadratic μ hQ u C) =ᵐ[μ]
      fun x => ∑ j, SobolevSpace.toLp μ hQ (u j) x * localGamma μ hQ (u j) (u i) x :=
    (localGamma_comm μ hQ (u i) _).trans (coordinateQuadratic_gradient μ hQ u C (u i) hu)
  have hall := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun i _ => hi i)
  filter_upwards [coordinateQuadratic_gradient μ hQ u C (coordinateQuadratic μ hQ u C) hu,
    hall] with x hx hix
  rw [hx]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hix i hi, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end RegularPointCoordinates

end

end OAI
