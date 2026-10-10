import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialHistories
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Entropy
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrdinaryPopulationSelection

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropy

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation
open JointPopulationRates JointOrdinaryPopulationSelection
open scoped BigOperators

abbrev PlacedInitial := Fin sortedInitial.length × Placement

theorem placement_read_card : ∀ s w : Fin 3,
    Fintype.card {phi : Placement // phi.symm s = w} = 2 := by
  decide +kernel

theorem sum_placement_read (s : Fin 3) (f : Fin 3 → ℝ) :
    (∑ phi : Placement, f (phi.symm s)) = 2 * ∑ w, f w := by
  classical
  rw [← Fintype.sum_fiberwise' (fun phi : Placement => phi.symm s) f]
  simp only [Finset.sum_const, Finset.card_univ, placement_read_card,
    nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]

def initialShapeCode (p : PlacedInitial) : JointPopulation.Shape :=
  rootShape ((0 : Fin 1), p.1) p.2

@[simp] theorem initialShapeCode_side (p : PlacedInitial) (s : Fin 3) :
    (JointPopulation.shapeSide s (initialShapeCode p)).val =
      sortedInitial.get p.1 (p.2.symm s) := by
  simp only [initialShapeCode, rootShape, encodePhysicalShape_side, initialShape]

@[simp] theorem rootShape_eq_initialShapeCode {K : ℕ} (j : Fin K)
    (g : Fin sortedInitial.length) (phi : Placement) :
    rootShape (j, g) phi = initialShapeCode (g, phi) := rfl

def placedInitialLaw : FiniteLaw PlacedInitial where
  mass p := (initialLaw (sortedInitial.get p.1) : ℝ) / 6
  nonneg p := div_nonneg (by
    exact_mod_cast (initialLaw_positive _ (List.get_mem _ _)).le) (by norm_num)
  total := by
    have hsum : (∑ g : Fin sortedInitial.length,
        (initialLaw (sortedInitial.get g) : ℝ)) = 1 := by
      exact_mod_cast initial_amount_sum 1 (0 : Fin 1)
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ,
      PhysicalOrders.card_physical_orders, nsmul_eq_mul]
    calc
      _ = ∑ g : Fin sortedInitial.length,
          (initialLaw (sortedInitial.get g) : ℝ) := by
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = 1 := hsum

def orderedInitialLaw : FiniteLaw JointPopulation.Shape :=
  placedInitialLaw.map initialShapeCode

def nativeInitialMarginal (k : Fin 17) : ℝ :=
  ∑ g : Fin sortedInitial.length,
    (initialLaw (sortedInitial.get g) : ℝ) *
      (∑ w : Fin 3, if sortedInitial.get g w = k.val then 1 else 0) / 3

def nativeH0 : ℝ := homogeneousEntropy nativeInitialMarginal

theorem nativeInitialMarginal_eq_list (k : Fin 17) :
    nativeInitialMarginal k =
      (sortedInitial.map (fun g => (initialLaw g : ℝ) *
        (∑ w : Fin 3, if g w = k.val then 1 else 0) / 3)).sum := by
  unfold nativeInitialMarginal
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem sortedInitial (fun g => (initialLaw g : ℝ) *
      (∑ w : Fin 3, if g w = k.val then 1 else 0) / 3))

theorem sideMass_orderedInitialLaw (s : Fin 3) (k : Fin 17) :
    sideMass orderedInitialLaw.mass s k =
      ∑ p : PlacedInitial,
        if JointPopulation.shapeSide s (initialShapeCode p) = k
          then placedInitialLaw.mass p else 0 := by
  classical
  unfold sideMass orderedInitialLaw
  simp only [FiniteLaw.map_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ p : PlacedInitial,
        if initialShapeCode p = u then
          if JointPopulation.shapeSide s u = k then placedInitialLaw.mass p else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem orderedInitialLaw_sideMass (s : Fin 3) :
    sideMass orderedInitialLaw.mass s = nativeInitialMarginal := by
  classical
  funext k
  rw [sideMass_orderedInitialLaw, Fintype.sum_prod_type]
  unfold nativeInitialMarginal
  apply Finset.sum_congr rfl
  intro g _
  have hside (phi : Placement) :
      JointPopulation.shapeSide s (initialShapeCode (g, phi)) = k ↔
        sortedInitial.get g (phi.symm s) = k.val := by
    rw [← Fin.val_inj, initialShapeCode_side]
  simp only [hside, placedInitialLaw]
  calc
    _ = ∑ phi : Placement, ((initialLaw (sortedInitial.get g) : ℝ) / 6) *
        (if sortedInitial.get g (phi.symm s) = k.val then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro phi _
      split_ifs <;> ring
    _ = ((initialLaw (sortedInitial.get g) : ℝ) / 6) *
        (2 * ∑ w : Fin 3, if sortedInitial.get g w = k.val then 1 else 0) := by
      rw [← Finset.mul_sum,
        sum_placement_read s (fun w : Fin 3 =>
          if sortedInitial.get g w = k.val then 1 else 0)]
    _ = _ := by ring

theorem nativeInitialMarginal_total : ∑ k, nativeInitialMarginal k = 1 := by
  rw [← orderedInitialLaw_sideMass 0, sideMass_total, orderedInitialLaw.total]

theorem nativeInitialMarginal_nonneg (k : Fin 17) : 0 ≤ nativeInitialMarginal k := by
  rw [← orderedInitialLaw_sideMass 0]
  simpa only [FiniteLaw.map_mass, sideMass] using
    (orderedInitialLaw.map (JointPopulation.shapeSide 0)).nonneg k

theorem nativeH0_eq_finiteEntropy : nativeH0 = finiteEntropy nativeInitialMarginal :=
  homogeneousEntropy_normalized _ nativeInitialMarginal_total

theorem orderedInitialLaw_side_entropy (s : Fin 3) :
    finiteEntropy (sideMass orderedInitialLaw.mass s) = nativeH0 := by
  rw [orderedInitialLaw_sideMass, nativeH0_eq_finiteEntropy]

theorem ordinary_capacity_per_lot :
    finiteEntropy orderedInitialLaw.mass -
      max (finiteEntropy orderedInitialLaw.mass -
          finiteEntropy (sideMass orderedInitialLaw.mass 0))
        (max (finiteEntropy orderedInitialLaw.mass -
            finiteEntropy (sideMass orderedInitialLaw.mass 1))
          (finiteEntropy orderedInitialLaw.mass -
            finiteEntropy (sideMass orderedInitialLaw.mass 2))) = nativeH0 := by
  simp only [orderedInitialLaw_side_entropy, max_self]
  ring

theorem ordinary_capacity_all_lots (K : ℕ) :
    entropyRate (fun _ : Fin K => 1) (fun _ => orderedInitialLaw) -
      degreeRate (fun _ : Fin K => 1) (fun _ => orderedInitialLaw) =
        (K : ℝ) * nativeH0 := by
  simp only [entropyRate, degreeRate, sideDegreeRate, one_mul,
    orderedInitialLaw_side_entropy, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, max_self]
  ring

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem initialJointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape) :
    (initialJointCounts allocation dilation j u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * orderedInitialLaw.mass u := by
  classical
  unfold initialJointCounts shapeCounts orderedInitialLaw
  simp only [FiniteLaw.map_mass, Nat.cast_sum, Finset.mul_sum,
    rootShape_eq_initialShapeCode]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : initialShapeCode p = u
  · simp only [hp, ite_true, population_cast_real, placedInitialLaw]
    congr 1
    simp only [amount, canonicalAmount, initialAmount, initialShape,
      Rat.cast_div, Rat.cast_ofNat]
  · simp [hp]

theorem initialJointCounts_ratio {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (j : Fin K) (u : JointPopulation.Shape) :
    (initialJointCounts allocation dilation j u : ℝ) /
      populationLength (K := K) allocation dilation = orderedInitialLaw.mass u := by
  classical
  rw [initialJointCounts_cast]
  have hp : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) hd))
  exact mul_div_cancel_left₀ _ hp

theorem initialJointCounts_sideMass {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (j : Fin K) (s : Fin 3) :
    sideMass (fun u => (initialJointCounts allocation dilation j u : ℝ) /
      populationLength (K := K) allocation dilation) s = nativeInitialMarginal := by
  simp only [initialJointCounts_ratio allocation hd, orderedInitialLaw_sideMass]

end MatrixMultiplication.AllFieldInitialEntropy

end

end OAI
