import OAI.Probability.SignedSweeps.OccupiedCounts

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma coefficientAction_layer {d : ℕ} (lam : Partition (2^d)) (i : Fin d)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    coefficientAction (spechtRepresentation lam)
      (subgroupAverageCoefficient (coordinateSubgroup d i)) = layerOperator lam i := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d)) (instDecidableEqFin _) (instDecidableEqFin _) (Fin.fintype _) (Fin.fintype _))
  rw [coefficientAction_subgroupAverage]
  rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

lemma coefficientPush_list (φ : G →* H) (L : List (G → ℂ)) :
    coefficientPush φ (coefficientListProduct L) =
      coefficientListProduct (L.map (coefficientPush φ)) := by
  induction L with
  | nil => exact coefficientPush_one φ
  | cons f L ih => simp only [coefficientListProduct, List.map_cons, coefficientPush_product, ih]

lemma productCoefficient_list {J : Type*} [Fintype J] (L : List (G → ℂ)) :
    productCoefficient (fun _ : J => coefficientListProduct L) =
      coefficientListProduct (L.map (fun f => productCoefficient (fun _ : J => f))) := by
  induction L with
  | nil => exact productCoefficient_one
  | cons f L ih => simp only [coefficientListProduct, List.map_cons, productCoefficient_product, ih]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def sweepCoefficient (d : ℕ) : SymmetricGroup (2^d) → ℂ :=
  coefficientListProduct ((List.ofFn (fun i : Fin d =>
    subgroupAverageCoefficient (coordinateSubgroup d i))).reverse)

lemma sweepCoefficient_action {d : ℕ} (lam : Partition (2^d)) :
    coefficientAction (spechtRepresentation lam) (sweepCoefficient d) = sweepOperator lam := by
  simp only [sweepCoefficient, coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, sweepOperator]

def sweepPowerCoefficient (d r : ℕ) (left : Bool) : SymmetricGroup (2^d) → ℂ :=
  coefficientPower (if left then
    coefficientProduct (sweepCoefficient d) (coefficientStar (sweepCoefficient d))
    else coefficientProduct (coefficientStar (sweepCoefficient d)) (sweepCoefficient d)) r

lemma sweepPowerCoefficient_positive (d r : ℕ) (left : Bool) :
    (coefficientAction finiteRegularRepresentation (sweepPowerCoefficient d r left)).IsPositive := by
  unfold sweepPowerCoefficient
  rw [coefficientAction_power]
  apply positive_pow
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte, coefficientAction_mul,
      coefficientAction_star (finiteRegularRepresentation (G:=SymmetricGroup (2^d)))
        finiteRegularRepresentation_norm]
    exact adjoint_mul_positive _
  · simp only [↓reduceIte, coefficientAction_mul,
      coefficientAction_star (finiteRegularRepresentation (G:=SymmetricGroup (2^d)))
        finiteRegularRepresentation_norm]
    simpa only [positiveSquare, LinearMap.adjoint_adjoint] using
      adjoint_mul_positive (coefficientAction finiteRegularRepresentation (sweepCoefficient d)).adjoint

lemma sweepPowerCoefficient_trace {d : ℕ} (lam : Partition (2^d)) (r : ℕ) (left : Bool) :
    LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam)
      (sweepPowerCoefficient d r left)) =
        LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r) := by
  unfold sweepPowerCoefficient
  rw [coefficientAction_power]
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte, coefficientAction_mul,
      coefficientAction_star _ (spechtRepresentation_norm lam), sweepCoefficient_action,
      sweepSquare, positiveSquare]
  · simp only [↓reduceIte, coefficientAction_mul,
      coefficientAction_star _ (spechtRepresentation_norm lam), sweepCoefficient_action]
    exact (trace_positiveSquare_orientations (sweepOperator lam) r).symm

def columnSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (columnEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient a))

def rowSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (rowEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient b))

lemma columnSweepCoefficient_layers (a b : ℕ) :
    columnSweepCoefficient a b = coefficientListProduct
      ((List.ofFn (fun i : Fin a => subgroupAverageCoefficient
        (coordinateSubgroup (a+b) (i.castAdd b)))).reverse) := by
  simp only [columnSweepCoefficient, sweepCoefficient, productCoefficient_list,
    coefficientPush_list, List.map_reverse, List.map_ofFn, Function.comp_def,
    ← column_layer_coefficient]

lemma rowSweepCoefficient_layers (a b : ℕ) :
    rowSweepCoefficient a b = coefficientListProduct
      ((List.ofFn (fun i : Fin b => subgroupAverageCoefficient
        (coordinateSubgroup (a+b) (i.natAdd a)))).reverse) := by
  simp only [rowSweepCoefficient, sweepCoefficient, productCoefficient_list,
    coefficientPush_list, List.map_reverse, List.map_ofFn, Function.comp_def,
    ← row_layer_coefficient]

lemma columnSweepCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) :
    coefficientAction (spechtRepresentation lam) (columnSweepCoefficient a b) = columnSweep lam := by
  rw [columnSweepCoefficient_layers]
  simp only [coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, columnSweep]

lemma rowSweepCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) :
    coefficientAction (spechtRepresentation lam) (rowSweepCoefficient a b) = rowSweep lam := by
  rw [rowSweepCoefficient_layers]
  simp only [coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, rowSweep]

def columnPowerCoefficient (a b r : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (columnEnumeration a b))
    (productCoefficient (fun _ => sweepPowerCoefficient a r true))

def rowPowerCoefficient (a b r : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (rowEnumeration a b))
    (productCoefficient (fun _ => sweepPowerCoefficient b r false))

lemma columnPowerCoefficient_formula (a b r : ℕ) : columnPowerCoefficient a b r =
    coefficientPower (coefficientProduct (columnSweepCoefficient a b)
      (coefficientStar (columnSweepCoefficient a b))) r := by
  simp only [columnPowerCoefficient, sweepPowerCoefficient, ↓reduceIte, productCoefficient_power,
    productCoefficient_product, productCoefficient_star, coefficientPush_power,
    coefficientPush_product, coefficientPush_star, columnSweepCoefficient]

lemma rowPowerCoefficient_formula (a b r : ℕ) : rowPowerCoefficient a b r =
    coefficientPower (coefficientProduct (coefficientStar (rowSweepCoefficient a b))
      (rowSweepCoefficient a b)) r := by
  simp only [rowPowerCoefficient, sweepPowerCoefficient, Bool.false_eq_true, ↓reduceIte,
    productCoefficient_power, productCoefficient_product, productCoefficient_star,
    coefficientPush_power, coefficientPush_product, coefficientPush_star, rowSweepCoefficient]

lemma columnPowerCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ) :
    coefficientAction (spechtRepresentation lam) (columnPowerCoefficient a b r) = columnSquarePower lam r := by
  simp only [columnPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ (spechtRepresentation_norm lam), columnSweepCoefficient_action,
    columnSquarePower]

lemma rowPowerCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ) :
    coefficientAction (spechtRepresentation lam) (rowPowerCoefficient a b r) = rowSquarePower lam r := by
  simp only [rowPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ (spechtRepresentation_norm lam), rowSweepCoefficient_action,
    rowSquarePower, positiveSquare]

lemma columnPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  rw [columnPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  apply positive_pow
  simpa only [positiveSquare, LinearMap.adjoint_adjoint] using
    adjoint_mul_positive (coefficientAction finiteRegularRepresentation (columnSweepCoefficient a b)).adjoint

lemma rowPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  rw [rowPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  exact positive_pow (adjoint_mul_positive _) r

lemma columnPowerCoefficient_support (a b r : ℕ) :
    ∀ g, g ∉ columnGroup a b → columnPowerCoefficient a b r g = 0 := by
  apply coefficientPush_support
  rintro g ⟨h,rfl⟩
  simpa only [columnGroup, columnEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
    Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Equiv.symm_symm,
    Prod.swap] using blockPermutation_fiber (columnEnumeration a b) h

lemma rowPowerCoefficient_support (a b r : ℕ) :
    ∀ g, g ∉ rowGroup a b → rowPowerCoefficient a b r g = 0 := by
  apply coefficientPush_support
  rintro g ⟨h,rfl⟩
  simpa only [rowGroup, rowEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
    Equiv.coe_fn_symm_mk, Equiv.symm_symm] using blockPermutation_fiber (rowEnumeration a b) h

end SignedSweeps
end

end OAI
