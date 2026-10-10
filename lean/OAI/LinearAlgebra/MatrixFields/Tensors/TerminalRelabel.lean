import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.ComplexArithmeticLowerBound

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication a b c = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_product_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r s : ℕ}
    (hT : RankAtMost (matrixCoefficients (K := K) A B C) r)
    (hS : RankAtMost (matrixCoefficients (K := K) D E F) s) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) (r * s) :=
  matrixCoefficients_rank_of_product (hT.product hS)

theorem matrixCoefficients_batch_rank [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r batches : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hfit : R ≤ batches * k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B)) (batches * r) :=
  matrixCoefficients_rank_of_product (houter.batch_product hbatch hfit)

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

theorem matrixCoefficients_cyclic_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {r : ℕ} (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) B C A) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  rw [← matrixCoefficients_cyclic (K := K) x y z]
  rw [congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

end Tensor






namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def directSumProductEquiv (ι κ X U : Type*) :
    ((ι × κ) × (X × U)) ≃ ((ι × X) × (κ × U)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [ite_eq_left hi, ite_eq_left hk, ite_eq_left (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [ite_eq_left hi, ite_eq_right hk, ite_eq_right hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [ite_eq_right hi, ite_eq_right hfull, zero_mul]

theorem RankAtMost.directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor K X Y Z} {S : κ → Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost (directSum T) r) (hS : RankAtMost (directSum S) s) :
    RankAtMost (directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2))) (r * s) := by
  have h := (hT.product hS).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  rw [Tensor.directSum_product] at h
  exact h

theorem directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    pullback (fun x : ι × X' => (x.1, fx x.2))
      (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))
      (directSum T) = directSum (fun i => pullback fx fy fz (T i)) := rfl

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

theorem RankAtMost.directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r) :
    RankAtMost (directSum (fun i => Tensor.cyclic (T i))) r := by
  rw [← Tensor.cyclic_directSum]
  exact h.cyclic

def directSumPowerEquiv (ι X : Type*) (n : ℕ) :
    ((Fin n → ι) × (Fin n → X)) ≃ (Fin n → ι × X) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

theorem RankAtMost.directSum_const_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum (fun _ : ι => T)) r)
    (n : ℕ) : RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) (r ^ n) :=
  (h.power n).directSum_const_of_power

section Rectangular

variable {A B C : Type*}

def rectangularSquareX (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((A × B) × (B × C)) × (C × A)) where
  toFun x := (((x.1.1, x.2.2.1), (x.1.2.1, x.2.2.2)), (x.1.2.2, x.2.1))
  invFun x := ((x.1.1.1, x.1.2.1, x.2.1), (x.2.2, x.1.1.2, x.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareY (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((B × C) × (C × A)) × (A × B)) where
  toFun y := (((y.1.2.1, y.2.2.2), (y.1.2.2, y.2.1)), (y.1.1, y.2.2.1))
  invFun y := ((y.2.1, y.1.1.1, y.1.2.1), (y.1.2.2, y.2.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareZ (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((C × A) × (A × B)) × (B × C)) where
  toFun z := (((z.1.2.2, z.2.1), (z.1.1, z.2.2.1)), (z.1.2.1, z.2.2.2))
  invFun z := ((z.1.2.1, z.2.1, z.1.1.1), (z.1.1.2, z.1.2.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

theorem matrixCoefficients_cyclic_product_square :
    pullback (rectangularSquareX A B C) (rectangularSquareY A B C)
      (rectangularSquareZ A B C)
      (product (product (matrixCoefficients (K := K) A B C)
        (matrixCoefficients B C A)) (matrixCoefficients C A B)) =
      matrixCoefficients (A × B × C) (A × B × C) (A × B × C) := by
  funext x y z
  dsimp only [pullback, rectangularSquareX, rectangularSquareY, rectangularSquareZ,
    product, matrixCoefficients]
  simp only [Prod.ext_iff, ite_mul, one_mul, zero_mul, ← ite_and]
  congr 1
  apply propext
  tauto

theorem cyclic_matrixCoefficients :
    cyclic (matrixCoefficients (K := K) A B C) = matrixCoefficients B C A := by
  funext x y z
  exact matrixCoefficients_cyclic x y z

theorem matrixCoefficients_symmetrized_rank {r : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K)
      (A × B × C) (A × B × C) (A × B × C)) (r ^ 3) := by
  have h' := ((h.product (matrixCoefficients_cyclic_rank h)).product
    (matrixCoefficients_cyclic_rank (matrixCoefficients_cyclic_rank h))).pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  rw [matrixCoefficients_cyclic_product_square] at h'
  simpa only [pow_succ, pow_zero, one_mul] using h'

theorem matrixCoefficients_directSum_symmetrized_rank
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : (ι × ι) × ι =>
      matrixCoefficients (K := K) (A × B × C) (A × B × C) (A × B × C))) (r ^ 3) := by
  have h₁ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
    simpa only [cyclic_matrixCoefficients] using h.directSum_cyclic
  have h₂ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) C A B)) r := by
    simpa only [cyclic_matrixCoefficients] using h₁.directSum_cyclic
  have h₃ := ((h.directSum_product h₁).directSum_product h₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  simpa only [matrixCoefficients_cyclic_product_square, pow_succ, pow_zero, one_mul] using h₃

theorem symmetrized_tag_card (ι : Type*) [Fintype ι] :
    Fintype.card ((ι × ι) × ι) = Fintype.card ι ^ 3 := by
  simp [Fintype.card_prod, pow_succ]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem symmetrized_index_card [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × B × C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  simp [Fintype.card_prod, mul_assoc]

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end




section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end




noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.TerminalRelabel

variable {K I A B C I' A' B' C' : Type*} [CommSemiring K]

def taggedPair (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) :
    I' × (A' × B') → I × (A × B) :=
  fun x => (eI x.1, (eA x.2.1, eB x.2.2))

theorem directSum_matrix_pullback
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.pullback (taggedPair eI eA eB) (taggedPair eI eB eC) (taggedPair eI eC eA)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  funext x y z
  simp only [Tensor.pullback, taggedPair, Tensor.directSum, Tensor.matrixCoefficients,
    eI.injective.eq_iff, eA.injective.eq_iff, eB.injective.eq_iff, eC.injective.eq_iff]

theorem directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.restrict
      (fun x s => if s = taggedPair eI eA eB x then (1 : K) else 0)
      (fun y s => if s = taggedPair eI eB eC y then (1 : K) else 0)
      (fun z s => if s = taggedPair eI eC eA z then (1 : K) else 0)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  rw [← Tensor.pullback_eq_restrict]
  exact directSum_matrix_pullback eI eA eB eC

theorem exists_directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    ∃ (a : (I' × (A' × B')) → (I × (A × B)) → K)
      (b : (I' × (B' × C')) → (I × (B × C)) → K)
      (c : (I' × (C' × A')) → (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') :=
  ⟨_, _, _, directSum_matrix_restrict_equiv eI eA eB eC⟩

theorem directSum_matrix_restrict_of_card_eq
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {L a b c : ℕ} (hI : Fintype.card I = L) (hA : Fintype.card A = a)
    (hB : Fintype.card B = b) (hC : Fintype.card C = c) :
    ∃ (aa : (Fin L × (Fin a × Fin b)) → (I × (A × B)) → K)
      (bb : (Fin L × (Fin b × Fin c)) → (I × (B × C)) → K)
      (cc : (Fin L × (Fin c × Fin a)) → (I × (C × A)) → K),
      Tensor.restrict aa bb cc
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin L =>
            Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) :=
  exists_directSum_matrix_restrict_equiv
    (Fintype.equivFinOfCardEq hI).symm (Fintype.equivFinOfCardEq hA).symm
    (Fintype.equivFinOfCardEq hB).symm (Fintype.equivFinOfCardEq hC).symm

theorem directSum_matrix_restrict_fin
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    ∃ (a : (Fin (Fintype.card I) × (Fin (Fintype.card A) × Fin (Fintype.card B))) →
        (I × (A × B)) → K)
      (b : (Fin (Fintype.card I) × (Fin (Fintype.card B) × Fin (Fintype.card C))) →
        (I × (B × C)) → K)
      (c : (Fin (Fintype.card I) × (Fin (Fintype.card C) × Fin (Fintype.card A))) →
        (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin (Fintype.card I) =>
            Tensor.matrixCoefficients (K := K)
              (Fin (Fintype.card A)) (Fin (Fintype.card B)) (Fin (Fintype.card C))) :=
  directSum_matrix_restrict_of_card_eq I A B C rfl rfl rfl rfl

end MatrixMultiplication.TerminalRelabel

end
end

end MatrixAllFields

end OAI
