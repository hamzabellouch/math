import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexPairingMatrixTensor
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchySeparationRates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexOrientationRates

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.BalancedSeparation

open scoped BigOperators
open Tensor LabelHierarchySeparation OrientationRates

section SinglePool

def singlePairingX (k : ℕ) : (Fin 1 × Fin k) ≃ Fin k where
  toFun x := x.2
  invFun x := (0, x)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

def singlePairingY (k : ℕ) : (Fin k × Fin 1) ≃ Fin k where
  toFun y := y.1
  invFun y := (y, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

def singlePairingZ : (Fin 1 × Fin 1) ≃ Unit where
  toFun _ := ()
  invFun _ := (0, 0)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

theorem singlePairing_matrix (k : ℕ) :
    pullback (singlePairingX k) (singlePairingY k) singlePairingZ
      (dotPairing (K := ℂ) (Fin k)) =
      matrixCoefficients (Fin 1) (Fin k) (Fin 1) := by
  funext x y z
  have hyz : y.2 = z.1 := Subsingleton.elim _ _
  have hzx : z.2 = x.1 := Subsingleton.elim _ _
  change (if x.2 = y.1 then (1 : ℂ) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [hyz, hzx, and_true]

theorem singlePairingXZ_matrix (k : ℕ) :
    pullback (singlePairingY k) singlePairingZ (singlePairingX k)
      (cyclic (dotPairing (K := ℂ) (Fin k))) =
      matrixCoefficients (Fin k) (Fin 1) (Fin 1) := by
  funext x y z
  have hxy : x.2 = y.1 := Subsingleton.elim _ _
  have hyz : y.2 = z.1 := Subsingleton.elim _ _
  change (if z.2 = x.1 then (1 : ℂ) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [hxy, hyz, true_and]

theorem singlePairingYZ_matrix (k : ℕ) :
    pullback singlePairingZ (singlePairingX k) (singlePairingY k)
      (cyclic (cyclic (dotPairing (K := ℂ) (Fin k)))) =
      matrixCoefficients (Fin 1) (Fin 1) (Fin k) := by
  funext x y z
  have hxy : x.2 = y.1 := Subsingleton.elim _ _
  have hzx : z.2 = x.1 := Subsingleton.elim _ _
  change (if y.2 = z.1 then (1 : ℂ) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [hxy, hzx, true_and, and_true]

theorem singlePairing_budget (k : ℕ) : 1 * k * 1 ≤ poolAuxiliaryCost k := by
  simpa only [one_mul, mul_one] using population_le_poolAuxiliaryCost k

end SinglePool

section MatrixBank

variable {K I : Type*} [CommSemiring K] [Fintype I] [DecidableEq I]
variable {A B C : I → Type*}
variable [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] [∀ i, DecidableEq (C i)]

def piPairEquiv (A B : I → Type*) :
    ((∀ i, A i) × (∀ i, B i)) ≃ (∀ i, A i × B i) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq I] in
theorem matrixBank_identity :
    pullback (piPairEquiv A B) (piPairEquiv B C) (piPairEquiv C A)
      (bankTensor (fun i => matrixCoefficients (K := K) (A i) (B i) (C i))) =
      matrixCoefficients (∀ i, A i) (∀ i, B i) (∀ i, C i) := by
  funext x y z
  change (∏ i, if x.2 i = y.1 i ∧ y.2 i = z.1 i ∧ z.2 i = x.1 i then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [Fintype.prod_boole, forall_and, ← funext_iff]

end MatrixBank

section PoolDimensions

variable {I : Type*} [Fintype I] [DecidableEq I]

def factorDimension (slot : I → Fin 3) (k : I → ℕ) (i : I) (s : Fin 3) : ℕ :=
  if slot i = s then k i else 1

def bankDimension (slot : I → Fin 3) (k : I → ℕ) (s : Fin 3) : ℕ :=
  ∏ i, factorDimension slot k i s

abbrev BankIndex (slot : I → Fin 3) (k : I → ℕ) (s : Fin 3) :=
  ∀ i, Fin (factorDimension slot k i s)

theorem card_BankIndex (slot : I → Fin 3) (k : I → ℕ) (s : Fin 3) :
    Fintype.card (BankIndex slot k s) = bankDimension slot k s := by
  simp only [BankIndex, Fintype.card_pi, Fintype.card_fin, bankDimension]

def bankIndexFinEquiv (slot : I → Fin 3) (k : I → ℕ) (s : Fin 3) :
    Fin (bankDimension slot k s) ≃ BankIndex slot k s :=
  (Fintype.equivFinOfCardEq (card_BankIndex slot k s)).symm

omit [DecidableEq I] in
theorem bank_volume (slot : I → Fin 3) (k : I → ℕ) :
    bankDimension slot k 0 * bankDimension slot k 1 * bankDimension slot k 2 =
      ∏ i, k i := by
  rw [← Fin.prod_univ_three (bankDimension slot k)]
  unfold bankDimension
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  simp [factorDimension]

omit [DecidableEq I] in
theorem bankDimension_pos (slot : I → Fin 3) (k : I → ℕ)
    (positive : ∀ i, 0 < k i) (s : Fin 3) : 0 < bankDimension slot k s := by
  apply Finset.prod_pos
  intro i hi
  unfold factorDimension
  split_ifs
  · exact positive i
  · exact Nat.zero_lt_one

omit [DecidableEq I] in
theorem bank_volume_le_auxiliary (slot : I → Fin 3) (k : I → ℕ) :
    bankDimension slot k 0 * bankDimension slot k 1 * bankDimension slot k 2 ≤
      ∏ i, poolAuxiliaryCost (k i) := by
  rw [bank_volume]
  exact Finset.prod_le_prod (fun i _ => population_le_poolAuxiliaryCost (k i))

def bankMatrixCoordinate (slot : I → Fin 3) (k : I → ℕ) (s t : Fin 3) :
    (Fin (bankDimension slot k s) × Fin (bankDimension slot k t)) ≃
      (∀ i, Fin (factorDimension slot k i s) × Fin (factorDimension slot k i t)) :=
  (Equiv.prodCongr (bankIndexFinEquiv slot k s) (bankIndexFinEquiv slot k t)).trans
    (piPairEquiv _ _)

def matrixBank (slot : I → Fin 3) (k : I → ℕ) :=
  bankTensor (fun i => matrixCoefficients (K := ℂ)
    (Fin (factorDimension slot k i 0)) (Fin (factorDimension slot k i 1))
    (Fin (factorDimension slot k i 2)))

theorem matrixBank_numeric (slot : I → Fin 3) (k : I → ℕ) :
    pullback (bankMatrixCoordinate slot k 0 1) (bankMatrixCoordinate slot k 1 2)
      (bankMatrixCoordinate slot k 2 0) (matrixBank slot k) =
      matrixCoefficients (Fin (bankDimension slot k 0))
        (Fin (bankDimension slot k 1)) (Fin (bankDimension slot k 2)) := by
  have h := matrixBank_identity (K := ℂ)
    (A := fun i => Fin (factorDimension slot k i 0))
    (B := fun i => Fin (factorDimension slot k i 1))
    (C := fun i => Fin (factorDimension slot k i 2))
  funext x y z
  have he := congrFun (congrFun (congrFun h
    (bankIndexFinEquiv slot k 0 x.1, bankIndexFinEquiv slot k 1 x.2))
    (bankIndexFinEquiv slot k 1 y.1, bankIndexFinEquiv slot k 2 y.2))
    (bankIndexFinEquiv slot k 2 z.1, bankIndexFinEquiv slot k 0 z.2)
  simpa only [pullback, matrixBank, bankMatrixCoordinate, Equiv.trans_apply,
    Equiv.prodCongr_apply, piPairEquiv, Equiv.coe_fn_mk, Prod.map_fst, Prod.map_snd,
    matrixCoefficients, Equiv.apply_eq_iff_eq] using he

def orientedPairingBank (slot : I → Fin 3) (k : I → ℕ) :=
  bankTensor (fun i => pairingTriple (K := ℂ)
    (Fin (factorDimension slot k i 0)) (Fin (factorDimension slot k i 1))
    (Fin (factorDimension slot k i 2)))

def pairingBankX (slot : I → Fin 3) (k : I → ℕ) :=
  (bankMatrixCoordinate slot k 0 1).trans
    (Equiv.piCongrRight fun i => pairingTripleMatrixX
      (Fin (factorDimension slot k i 0)) (Fin (factorDimension slot k i 1)))

def pairingBankY (slot : I → Fin 3) (k : I → ℕ) :=
  (bankMatrixCoordinate slot k 1 2).trans
    (Equiv.piCongrRight fun i => pairingTripleMatrixY
      (Fin (factorDimension slot k i 1)) (Fin (factorDimension slot k i 2)))

def pairingBankZ (slot : I → Fin 3) (k : I → ℕ) :=
  (bankMatrixCoordinate slot k 2 0).trans
    (Equiv.piCongrRight fun i => pairingTripleMatrixZ
      (Fin (factorDimension slot k i 2)) (Fin (factorDimension slot k i 0)))

theorem orientedPairingBank_numeric (slot : I → Fin 3) (k : I → ℕ) :
    pullback (pairingBankX slot k) (pairingBankY slot k) (pairingBankZ slot k)
      (orientedPairingBank slot k) =
      matrixCoefficients (Fin (bankDimension slot k 0))
        (Fin (bankDimension slot k 1)) (Fin (bankDimension slot k 2)) := by
  rw [← matrixBank_numeric slot k]
  funext x y z
  apply Finset.prod_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun
    (pairingTriple_matrixCoefficients (K := ℂ)
      (A := Fin (factorDimension slot k i 0))
      (B := Fin (factorDimension slot k i 1))
      (C := Fin (factorDimension slot k i 2)))
    (bankMatrixCoordinate slot k 0 1 x i))
    (bankMatrixCoordinate slot k 1 2 y i))
    (bankMatrixCoordinate slot k 2 0 z i)

theorem orientedPairingBank_directSum_rank {Label : Type*} [DecidableEq Label]
    (slot : I → Fin 3) (k : I → ℕ) {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => orientedPairingBank slot k)) r) :
    RankAtMost (directSum (fun _ : Label =>
      matrixCoefficients (K := ℂ) (Fin (bankDimension slot k 0))
        (Fin (bankDimension slot k 1)) (Fin (bankDimension slot k 2)))) r := by
  have hp := h.directSum_pullback (pairingBankX slot k) (pairingBankY slot k)
    (pairingBankZ slot k)
  simpa only [orientedPairingBank_numeric] using hp

theorem orientedPairingBank_directSum_borderRank {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (slot : I → Fin 3) (k : I → ℕ) {r : ℕ}
    (h : BorderRankAtMost
      (directSum (fun _ : Label => orientedPairingBank slot k)) r) :
    BorderRankAtMost (directSum (fun _ : Label =>
      matrixCoefficients (K := ℂ) (Fin (bankDimension slot k 0))
        (Fin (bankDimension slot k 1)) (Fin (bankDimension slot k 2)))) r := by
  classical
  have heq := directSum_pullback (fun _ : Label => orientedPairingBank slot k)
    (pairingBankX slot k) (pairingBankY slot k) (pairingBankZ slot k)
  simp only [orientedPairingBank_numeric] at heq
  rw [← heq, pullback_eq_restrict]
  exact h.restrict _ _ _

end PoolDimensions

section SixOrientations

variable {I : Type*} [Fintype I] [DecidableEq I]

def physicalPairingSlot (orientation : Orientation) : Fin 3 :=
  if orientation 1 = 2 then 0 else if orientation 2 = 2 then 1 else 2

theorem physicalPairingSlot_fiber_card : ∀ s : Fin 3,
    Fintype.card {orientation : Orientation // physicalPairingSlot orientation = s} = 2 := by
  decide

theorem physicalPairingSlot_product (k : ℕ) (s : Fin 3) :
    (∏ orientation : Orientation, if physicalPairingSlot orientation = s then k else 1) =
      k ^ 2 := by
  rw [← Finset.prod_filter]
  rw [Finset.prod_const]
  have h := physicalPairingSlot_fiber_card s
  rw [Fintype.card_subtype] at h
  rw [h]

def sixSlot (relative : I → Orientation) (i : Orientation × I) : Fin 3 :=
  physicalPairingSlot (i.1 * relative i.2)

omit [DecidableEq I] in
theorem six_bankDimension (relative : I → Orientation) (k : I → ℕ) (s : Fin 3) :
    bankDimension (sixSlot relative) (fun i : Orientation × I => k i.2) s =
      (∏ i, k i) ^ 2 := by
  unfold bankDimension factorDimension sixSlot
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  calc
    _ = ∏ i, (k i) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      calc
        _ = ∏ orientation : Orientation,
            if physicalPairingSlot orientation = s then k i else 1 :=
          prod_relative_orientation (relative i)
            (fun orientation => if physicalPairingSlot orientation = s then k i else 1)
        _ = _ := physicalPairingSlot_product (k i) s
    _ = _ := Finset.prod_pow _ _ _

omit [DecidableEq I] in
theorem six_bank_volume (relative : I → Orientation) (k : I → ℕ) :
    bankDimension (sixSlot relative) (fun i : Orientation × I => k i.2) 0 *
        bankDimension (sixSlot relative) (fun i : Orientation × I => k i.2) 1 *
        bankDimension (sixSlot relative) (fun i : Orientation × I => k i.2) 2 =
      (∏ i, k i) ^ 6 := by
  rw [six_bankDimension, six_bankDimension, six_bankDimension]
  ring

omit [DecidableEq I] in
theorem six_bank_budget (k : I → ℕ) :
    (∏ i, k i) ^ 6 ≤ (∏ i, poolAuxiliaryCost (k i)) ^ 6 := by
  exact pow_le_pow_left'
    (Finset.prod_le_prod (fun i _ => population_le_poolAuxiliaryCost (k i))) 6

omit [DecidableEq I] in
theorem six_auxiliary_product (k : I → ℕ) :
    (∏ i : Orientation × I, poolAuxiliaryCost (k i.2)) =
      (∏ i, poolAuxiliaryCost (k i)) ^ 6 := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const, Finset.card_univ, orientation_card]

def orientationBankEquiv (relative : I → Orientation) :
    (Orientation × I) ≃ (Orientation × I) where
  toFun x := (x.1 * relative x.2, x.2)
  invFun x := (x.1 * (relative x.2)⁻¹, x.2)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem orientationBankEquiv_site (relative : I → Orientation)
    (x : Orientation × I) : (orientationBankEquiv relative x).2 = x.2 := rfl

def orientationCoordinateEquiv (relative : I → Orientation) (F : Type*) :
    ((Orientation × I) → F) ≃ ((Orientation × I) → F) where
  toFun word site := word (orientationBankEquiv relative site)
  invFun word site := word ((orientationBankEquiv relative).symm site)
  left_inv word := by
    funext site
    simp
  right_inv word := by
    funext site
    simp

omit [DecidableEq I] in
theorem orientationCoordinateEquiv_tensor {K X Y Z : Type*} [CommSemiring K]
    (relative : I → Orientation) (T : Tensor K X Y Z) :
    pullback (orientationCoordinateEquiv relative X)
      (orientationCoordinateEquiv relative Y) (orientationCoordinateEquiv relative Z)
      (bankTensor (fun _ : Orientation × I => T)) =
      bankTensor (fun _ : Orientation × I => T) := by
  funext x y z
  exact (orientationBankEquiv relative).prod_comp (fun site => T (x site) (y site) (z site))

omit [DecidableEq I] in
theorem orientationBankEquiv_grade_card {Grade : Type*} [DecidableEq Grade]
    (relative : I → Orientation) (word : Orientation × I → Grade)
    (orientation : Orientation) (grade : Grade) :
    Fintype.card {x : Orientation × I //
      (orientationBankEquiv relative x).1 = orientation ∧
        word (orientationBankEquiv relative x) = grade} =
      Fintype.card {x : Orientation × I // x.1 = orientation ∧ word x = grade} :=
  Fintype.card_congr ((orientationBankEquiv relative).subtypeEquiv fun _ => Iff.rfl)

end SixOrientations
end MatrixMultiplication.Foundation.BalancedSeparation

end

end OAI
