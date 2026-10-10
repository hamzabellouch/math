import Mathlib
import OAI.Analysis.LaughlinGap.FourAveraging

namespace OAI

/-! Four Highest. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma sum_increasing_matrices {n : ℕ} {κ : Type*} (f : Fin n → Fin n → Matrix κ κ ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (2:ℝ) • (∑ a : Occupation.PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, f i j := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Occupation.sum_increasing_pairs (fun i j => f i j x y)
    (fun i j => congrFun (congrFun (hs i j) x) y)
    (fun i => congrFun (congrFun (hd i) x) y)

lemma annihilation_square_zero {n : ℕ} (i : Fin n) : annihilation i * annihilation i = 0 := by
  apply complexify_injective
  rw [map_mul, map_zero, complexify_annihilation]
  exact Occupation.transition_square i false

lemma fourAnnihilator_exterior {Q D T r : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hD : D ≤ T) (hr : r ≤ D) (ho : Odd r) :
    fourAnnihilator Q D T r =
      ∑ p : Fin (2*Q-2+1), ∑ a : Occupation.PairLabel (Q+1),
        fourBodyCoefficient Q D T r p.val a.val.1.val a.val.2.val •
          (annihilation a.val.2 * annihilation a.val.1 * physicalPair Q p.val) := by
  classical
  simp only [fourAnnihilator, combination, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  have hf (j k : Fin (Q+1)) :
      nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(k,j)) =
        -nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) := by
    rw [nestedTensor_flip _ _ _ _ _ (by omega) (by omega), ho.neg_one_pow, neg_one_mul]
  let f := fun j k : Fin (Q+1) =>
    nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) • physicalFour Q (p,(j,k))
  have hs (j k : Fin (Q+1)) : f j k = f k j := by
    dsimp [f]
    rw [hf, physicalFour_flip, neg_smul, smul_neg, neg_neg]
  have hd (j : Fin (Q+1)) : f j j = 0 := by
    simp [f, physicalFour, productFamily, annihilation_square_zero]
  rw [← sum_increasing_matrices f hs hd, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [f]
  rw [physicalFour, productFamily, productFamily, smul_smul, smul_smul,
    ← lowNested_coefficient hr hD hT (p,(a.val.1,a.val.2))]
  congr 1
  have hn := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  rw [hn]
  ring

lemma fourAnnihilator_weight_local {Q D T r : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hD : D ≤ T) (hr : r ≤ D) (ho : Odd r) :
    fourAnnihilator Q D T r =
      ∑ a : {a : Fin (2*Q-2+1) × Occupation.PairLabel (Q+1) //
        a.1.val+a.2.val.1.val+a.2.val.2.val=T},
        fourBodyCoefficient Q D T r a.val.1.val a.val.2.val.1.val a.val.2.val.2.val •
          (annihilation a.val.2.val.2 * annihilation a.val.2.val.1 * physicalPair Q a.val.1.val) := by
  classical
  rw [fourAnnihilator_exterior hQ hT hD hr ho]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin (2*Q-2+1) ×
    Occupation.PairLabel (Q+1) => a.1.val+a.2.val.1.val+a.2.val.2.val=T)) (by simp)
    (fun a => fourBodyCoefficient Q D T r a.1.val a.2.val.1.val a.2.val.2.val •
      (annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val))]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro b hb
  let a := (p,b)
  change _ = if a.1.val+a.2.val.1.val+a.2.val.2.val=T then _ else _
  by_cases h : a.1.val+a.2.val.1.val+a.2.val.2.val=T
  · simp [h]
  · dsimp [a] at h
    simp [fourBodyCoefficient, h, a]

end LaughlinGap.RealOccupation

end

end OAI
