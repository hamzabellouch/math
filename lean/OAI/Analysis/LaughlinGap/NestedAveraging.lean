import Mathlib
import OAI.Analysis.LaughlinGap.IntertwinerAveraging
import OAI.Analysis.LaughlinGap.NestedSpin
import OAI.Analysis.LaughlinGap.PairDecomposition
import OAI.Analysis.LaughlinGap.PhysicalAveraging

namespace OAI

/-! Nested Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def LadderMap.changeSource {n d : ℕ} {S : LadderSystem ι} (h : n=d)
    (A : LadderMap (standardLadderSystem n) S) : LadderMap (standardLadderSystem d) S :=
  h ▸ A

lemma LadderMap.changeSource_single {n d : ℕ} {S : LadderSystem ι} (h : n=d)
    (A : LadderMap (standardLadderSystem n) S) (i : Fin (d+1)) :
    (A.changeSource h).toLinearMap (Pi.single i 1) =
      A.toLinearMap (Pi.single (⟨i.val,by omega⟩ : Fin (n+1)) 1) := by
  subst d
  rfl

lemma nestedTensor_weight_support (n m k r z l : ℕ)
    (a : Fin (n+1) × (Fin (m+1) × Fin (k+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val ≠ r+z+l) : nestedTensor n m k r z l a = 0 := by
  unfold nestedTensor
  apply Finset.sum_eq_zero
  intro q hq
  simp only [coupledTensor]
  split_ifs with h₁ h₂ h₂ <;> try simp
  exfalso
  apply ha
  omega

lemma nestedTensor_flip (n Q r z l : ℕ) (hr : r ≤ Q) (_hl : l ≤ n+(2*Q-2*r)-2*z)
    (a : Fin (n+1)) (j k : Fin (Q+1)) :
    nestedTensor n Q Q r z l (a,(k,j)) = (-1:ℝ)^r * nestedTensor n Q Q r z l (a,(j,k)) := by
  unfold nestedTensor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coupledTensor_swap hr (Nat.le_of_lt_succ q.isLt)]
  ring

noncomputable def nestedAtDeficit {n m k D r : ℕ} (hr : r ≤ min m k) (hrD : r ≤ D)
    (hz : D-r ≤ min n (m+k-2*r)) :
    LadderMap (standardLadderSystem (n+m+k-2*D)) (nestedSpin n m k) :=
  (nestedEmbedding hr hz).changeSource (by omega)

lemma nestedAtDeficit_single {n m k D r : ℕ} (hr : r ≤ min m k) (hrD : r ≤ D)
    (hz : D-r ≤ min n (m+k-2*r)) (l : Fin (n+m+k-2*D+1)) :
    (nestedAtDeficit hr hrD hz).toLinearMap (Pi.single l 1) =
      nestedTensor n m k r (D-r) l.val := by
  rw [nestedAtDeficit, LadderMap.changeSource_single, nestedEmbedding_apply]
  simp [Pi.single_apply, ite_smul]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma Covariant.equal_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n : ℕ}
    (A C : LadderMap (standardLadderSystem n) S) (i j : Fin (n+1)) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap (Pi.single i 1))).transpose *
        combination B (C.toLinearMap (Pi.single j 1))) =
      if i=j then average (rotationCommutant L)
        ((combination B (A.toLinearMap (Pi.single (0 : Fin (n+1)) 1))).transpose *
          combination B (C.toLinearMap (Pi.single (0 : Fin (n+1)) 1))) else 0 := by
  simp only [← lift_rankOne, h.average_lift, equal_copy_average, map_smul]
  split_ifs <;> simp

lemma Covariant.distinct_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n m : ℕ}
    (hnm : n ≠ m) (A : LadderMap (standardLadderSystem n) S)
    (C : LadderMap (standardLadderSystem m) S) (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap x)).transpose * combination B (C.toLinearMap y)) = 0 := by
  rw [← lift_rankOne, h.average_lift, distinct_copy_average hnm, map_zero]

noncomputable def physicalFour (Q : ℕ) :
    (Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) → FockMatrix (Q+1) :=
  fun a => (1/Real.sqrt 2) •
    productFamily (fun p => physicalPair Q p.val) (productFamily annihilation annihilation) a

lemma physicalFour_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (nestedSpin (2*Q-2) Q Q)) (physicalFour Q) :=
  ((physicalPair_covariant hQ).product ((annihilation_covariant _).product
    (annihilation_covariant _))).smul (1/Real.sqrt 2)

lemma annihilation_anticommute' {n : ℕ} (j k : Fin n) :
    annihilation k * annihilation j = -(annihilation j * annihilation k) := by
  apply complexify_injective
  simpa only [map_mul, map_neg, complexify_annihilation] using
    Occupation.annihilation_anticommute k j

lemma physicalFour_flip (Q : ℕ) (a : Fin (2*Q-2+1)) (j k : Fin (Q+1)) :
    physicalFour Q (a,(k,j)) = -physicalFour Q (a,(j,k)) := by
  simp only [physicalFour, productFamily]
  rw [annihilation_anticommute' k j, neg_mul, smul_neg]

lemma four_combination_flip (Q : ℕ)
    (x : (Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) → ℝ) :
    combination (physicalFour Q) (fun a => x (a.1,(a.2.2,a.2.1))) =
      -combination (physicalFour Q) x := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [physicalFour_flip, smul_neg]

lemma physicalFour_even_null {Q r z l : ℕ} (hr : r ≤ Q) (he : Even r)
    (hl : l ≤ (2*Q-2)+(2*Q-2*r)-2*z) :
    combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r z l) = 0 := by
  have hf : (fun a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) =>
      nestedTensor (2*Q-2) Q Q r z l (a.1,(a.2.2,a.2.1))) =
      nestedTensor (2*Q-2) Q Q r z l := by
    funext a
    rw [nestedTensor_flip _ _ _ _ _ hr hl, he.neg_one_pow, one_mul]
  have hh := four_combination_flip Q (nestedTensor (2*Q-2) Q Q r z l)
  rw [hf] at hh
  have h2 : (2:ℝ) • combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r z l) = 0 := by
    rw [two_smul ℝ]
    exact eq_neg_iff_add_eq_zero.mp hh
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end LaughlinGap.RealOccupation

end

end OAI
