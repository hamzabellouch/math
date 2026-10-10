import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialOrbit
import Mathlib.Data.Rat.BigOperators

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialGibbs

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy AllFieldInitialOrbit
open MatrixMultiplication.Foundation
open scoped BigOperators

def coordinateWeight (k : Fin 17) : ℝ :=
  (weight (initialInteger k.val) : ℝ)

def orderedWeight (u : JointPopulation.Shape) : ℝ :=
  ∏ s : Fin 3, coordinateWeight (JointPopulation.shapeSide s u)

def initialNormalizer : ℝ := ((sortedInitial.map initialWeight).sum : ℚ)

def initialPotential (k : Fin 17) : ℝ := Real.log (coordinateWeight k)

def initialLogNormalizer : ℝ := Real.log initialNormalizer

theorem coordinateWeight_pos (k : Fin 17) : 0 < coordinateWeight k := by
  apply Rat.cast_pos.mpr
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem orderedWeight_pos (u : JointPopulation.Shape) : 0 < orderedWeight u :=
  Finset.prod_pos (fun _ _ => coordinateWeight_pos _)

theorem initialNormalizer_pos : 0 < initialNormalizer := by
  apply Rat.cast_pos.mpr
  exact list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s)

theorem orderedWeight_source (p : PlacedInitial) :
    orderedWeight (initialShapeCode p) =
      ∏ s : Fin 3, (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ) := by
  simp only [orderedWeight, coordinateWeight, initialShapeCode_side]
  exact p.2.symm.prod_comp
    (fun s : Fin 3 => (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ))

theorem initialWeight_source (p : PlacedInitial) :
    (initialWeight (sortedInitial.get p.1) : ℝ) =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) := by
  rw [orderedWeight_source]
  simp only [initialWeight]
  push_cast
  rfl

theorem placedInitialLaw_mass (p : PlacedInitial) :
    placedInitialLaw.mass p =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) / initialNormalizer / 6 := by
  change (initialLaw (sortedInitial.get p.1) : ℝ) / 6 = _
  rw [initialLaw, ite_eq_left (List.get_mem _ _), Rat.cast_div, initialWeight_source p]
  rfl

theorem orderedInitialLaw_mass (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    orderedInitialLaw.mass u = orderedWeight u / initialNormalizer := by
  classical
  have hcount : (∑ p : PlacedInitial,
      if initialShapeCode p = u then
        (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) = 6 := by
    exact_mod_cast weighted_fiber_count u hu
  simp only [orderedInitialLaw, FiniteLaw.map_mass, placedInitialLaw_mass]
  calc
    _ = (∑ p : PlacedInitial, if initialShapeCode p = u then
          (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) *
        (orderedWeight u / initialNormalizer / 6) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : initialShapeCode p = u
      · simp only [hp, ite_true]
        ring
      · simp only [hp, ite_false, zero_mul]
    _ = _ := by rw [hcount]; ring

theorem orderedInitialLaw_zero (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val ≠ 16) :
    orderedInitialLaw.mass u = 0 := by
  classical
  simp only [orderedInitialLaw, FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  intro hp
  have ht := source_total p
  rw [hp] at ht
  exact hu ht

theorem orderedInitialLaw_mass_eq (u : JointPopulation.Shape) :
    orderedInitialLaw.mass u =
      if u.1.val + u.2.1.val + u.2.2.val = 16
        then orderedWeight u / initialNormalizer else 0 := by
  split_ifs with hu
  · exact orderedInitialLaw_mass u hu
  · exact orderedInitialLaw_zero u hu

theorem orderedInitialLaw_positive (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    0 < orderedInitialLaw.mass u := by
  rw [orderedInitialLaw_mass u hu]
  exact div_pos (orderedWeight_pos u) initialNormalizer_pos

theorem orderedInitialLaw_support (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  by_contra hn
  rw [orderedInitialLaw_zero u hn] at hu
  exact lt_irrefl _ hu

theorem log_orderedWeight (u : JointPopulation.Shape) :
    Real.log (orderedWeight u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) := by
  rw [orderedWeight, Real.log_prod
    (fun s _ => ne_of_gt (coordinateWeight_pos (JointPopulation.shapeSide s u)))]
  simp only [Fin.sum_univ_three, initialPotential]

theorem orderedInitialLaw_log (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    Real.log (orderedInitialLaw.mass u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) - initialLogNormalizer := by
  rw [orderedInitialLaw_mass u (orderedInitialLaw_support u hu),
    Real.log_div (ne_of_gt (orderedWeight_pos u)) (ne_of_gt initialNormalizer_pos),
    log_orderedWeight]
  rfl

end MatrixMultiplication.AllFieldInitialGibbs

end

end OAI
