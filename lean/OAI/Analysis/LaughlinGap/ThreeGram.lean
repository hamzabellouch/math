import Mathlib
import OAI.Analysis.LaughlinGap.ThreeSpectrum

namespace OAI

/-! Three Gram. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

abbrev ThreeIndex (ι : Type*) := (ι × ι) × ι

def cycleIndex (ι : Type*) : ThreeIndex ι ≃ ThreeIndex ι where
  toFun t := ((t.1.2,t.2),t.1.1)
  invFun t := ((t.2,t.1.1),t.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def cycleMap (ι : Type*) : Module.End ℝ (ThreeIndex ι → ℝ) where
  toFun x t := x (cycleIndex ι t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cycleMap_apply {ι : Type*} (x : ThreeIndex ι → ℝ) (i j k : ι) :
    cycleMap ι x ((i,j),k) = x ((j,k),i) := rfl

@[simp] lemma cycleMap_cube {ι : Type*} (x : ThreeIndex ι → ℝ) :
    cycleMap ι (cycleMap ι (cycleMap ι x)) = x := rfl

lemma cycleMap_dot {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cycleMap ι x) (cycleMap ι y) = dotProduct x y := by
  exact (cycleIndex ι).sum_comp (fun t => x t * y t)

lemma cycleMap_adjoint {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cycleMap ι x) y = dotProduct x (cycleMap ι (cycleMap ι y)) := by
  simpa only [cycleMap_cube] using cycleMap_dot x (cycleMap ι (cycleMap ι y))

def cyclicSum (ι : Type*) : Module.End ℝ (ThreeIndex ι → ℝ) :=
  LinearMap.id + cycleMap ι + (cycleMap ι).comp (cycleMap ι)

@[simp] lemma cyclicSum_apply {ι : Type*} (x : ThreeIndex ι → ℝ) :
    cyclicSum ι x = x + cycleMap ι x + cycleMap ι (cycleMap ι x) := rfl

lemma cyclicSum_dot {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cyclicSum ι x) (cyclicSum ι y) =
      3 * (dotProduct x y + dotProduct x (cycleMap ι y) +
        dotProduct x (cycleMap ι (cycleMap ι y))) := by
  simp only [cyclicSum_apply, add_dotProduct, dotProduct_add,
    cycleMap_adjoint, cycleMap_cube]
  ring

lemma pairSpectatorInclusion_antisymmetric {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (i j k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).toLinearMap a ((j,i),k) =
      -(pairSpectatorInclusion hQ).toLinearMap a ((i,j),k) := by
  simp only [pairSpectatorInclusion_apply, pairCoefficient_swap Q _ j i,
    neg_mul, Finset.sum_neg_distrib, neg_neg]

lemma pairSpectatorInclusion_isometry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      ((pairSpectatorInclusion hQ).toLinearMap b) = dotProduct a b := by
  have hab (p r : Fin (2*Q-2+1)) :
      (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        pairCoefficient Q p.val i j * pairCoefficient Q r.val i j) =
        if p=r then 1 else 0 := by
    split_ifs with hh
    · subst r
      simpa only [← sq] using pairCoefficient_sum_sq Q p.val hQ (by omega)
    · exact pairCoefficient_sum_mul_of_ne Q p.val r.val (fun he => hh (Fin.ext he))
  classical
  have hfixed (aa bb : Fin (2*Q-2+1) → ℝ) :
      (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        (∑ p, pairCoefficient Q p.val i j * aa p) *
          (∑ r, pairCoefficient Q r.val i j * bb r)) = ∑ p, aa p * bb p := by
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    let f := fun (i j : Fin (Q+1)) (p r : Fin (2*Q-2+1)) =>
      pairCoefficient Q p.val i j * aa p * (pairCoefficient Q r.val i j * bb r)
    change (∑ i, ∑ j, ∑ p, ∑ r, f i j p r) = _
    calc
      _ = ∑ i, ∑ p, ∑ j, ∑ r, f i j p r := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ p, ∑ i, ∑ j, ∑ r, f i j p r := Finset.sum_comm
      _ = ∑ p, ∑ i, ∑ r, ∑ j, f i j p r := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ p, ∑ r, ∑ i, ∑ j, f i j p r := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_comm
      _ = ∑ p, ∑ r, (∑ i, ∑ j,
          pairCoefficient Q p.val i j * pairCoefficient Q r.val i j) * (aa p * bb r) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [f]
        ring
      _ = _ := by simp [hab]
  simp only [dotProduct, Fintype.sum_prod_type, pairSpectatorInclusion_apply]
  let f := fun (i j k : Fin (Q+1)) =>
    (∑ p : Fin (2*Q-2+1), pairCoefficient Q p.val i j * a (p,k)) *
      (∑ r : Fin (2*Q-2+1), pairCoefficient Q r.val i j * b (r,k))
  change (∑ i, ∑ j, ∑ k, f i j k) = _
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ p, a (p,k)*b (p,k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hfixed (fun p => a (p,k)) (fun p => b (p,k))
    _ = _ := Finset.sum_comm

noncomputable def orderedThreeWedge {Q : ℕ} (hQ : 2 ≤ Q) :
    ((Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) →ₗ[ℝ]
      (ThreeIndex (Fin (Q+1)) → ℝ) :=
  (Real.sqrt 3)⁻¹ • ((cyclicSum (Fin (Q+1))).comp (pairSpectatorInclusion hQ).toLinearMap)

lemma swap23Linear_adjoint (Q : ℕ)
    (x y : ThreeIndex (Fin (Q+1)) → ℝ) :
    dotProduct (swap23Linear Q x) y = dotProduct x (swap23Linear Q y) := by
  let e : ThreeIndex (Fin (Q+1)) ≃ ThreeIndex (Fin (Q+1)) := {
    toFun := fun t => ((t.1.1,t.2),t.1.2)
    invFun := fun t => ((t.1.1,t.2),t.1.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact e.sum_comp (fun t => x t * swap23Linear Q y t)

lemma cycleSquare_pairSpectatorInclusion {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    cycleMap (Fin (Q+1)) (cycleMap (Fin (Q+1))
      ((pairSpectatorInclusion hQ).toLinearMap a)) =
      -(swap23Linear Q ((pairSpectatorInclusion hQ).toLinearMap a)) := by
  funext ⟨⟨i,j⟩,k⟩
  exact pairSpectatorInclusion_antisymmetric hQ a i k j

lemma cyclicSum_pair_dot {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct (cyclicSum (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap a))
      (cyclicSum (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap b)) =
      3 * (dotProduct a b - 2 * dotProduct a ((compressedSwap hQ).toLinearMap b)) := by
  have hab : dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      (swap23Linear Q ((pairSpectatorInclusion hQ).toLinearMap b)) =
      dotProduct a ((compressedSwap hQ).toLinearMap b) :=
    transposeMap_adjoint (pairSpectatorInclusion hQ).toLinearMap a _
  have hc : dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      (cycleMap (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap b)) =
      - dotProduct a ((compressedSwap hQ).toLinearMap b) := by
    rw [dotProduct_comm, cycleMap_adjoint,
      cycleSquare_pairSpectatorInclusion, dotProduct_neg, dotProduct_comm,
      swap23Linear_adjoint, hab]
  rw [cyclicSum_dot, pairSpectatorInclusion_isometry, hc,
    cycleSquare_pairSpectatorInclusion, dotProduct_neg, hab]
  ring

theorem orderedThreeWedge_dot {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct (orderedThreeWedge hQ a) (orderedThreeWedge hQ b) =
      dotProduct a b - 2 * dotProduct a ((compressedSwap hQ).toLinearMap b) := by
  simp only [orderedThreeWedge, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, cyclicSum_pair_dot]
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hs]

noncomputable def orderedThreeGram {Q : ℕ} (hQ : 2 ≤ Q) :
    Module.End ℝ ((Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :=
  (transposeMap (orderedThreeWedge hQ)).comp (orderedThreeWedge hQ)

theorem orderedThreeGram_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    orderedThreeGram hQ a = a - (2 : ℝ) • (compressedSwap hQ).toLinearMap a := by
  apply eq_of_dotProduct_eq
  intro b
  change dotProduct b (transposeMap (orderedThreeWedge hQ) (orderedThreeWedge hQ a)) = _
  rw [← transposeMap_adjoint, orderedThreeWedge_dot,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem orderedThreeGram_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    orderedThreeGram hQ (coupledTensor (2*Q-2) Q z l) =
      (1+threeBodyGramCoefficient Q z) • coupledTensor (2*Q-2) Q z l := by
  rw [orderedThreeGram_apply, compressedSwap_eigenvalue hQ hz hl]
  funext pq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem orderedThreeGram_defect_expansion {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    orderedThreeGram hQ a - a =
      ∑ i : CoupledIndex (2*Q-2) Q,
        (threeBodyGramCoefficient Q i.1.val *
          dotProduct (coupledTensor (2*Q-2) Q i.1.val i.2.val) a) •
            coupledTensor (2*Q-2) Q i.1.val i.2.val := by
  let D := orderedThreeGram hQ - LinearMap.id
  change D a = _
  conv_lhs => rw [← coupledTensor_expansion (2*Q-2) Q a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  dsimp [D]
  rw [orderedThreeGram_eigenvalue hQ (by have := i.1.isLt; omega)
    (Nat.le_of_lt_succ i.2.isLt)]
  funext pq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma threeBodyGramCoefficient_zero (Q : ℕ) : threeBodyGramCoefficient Q 0 = -1 := by
  norm_num [threeBodyGramCoefficient, fallingRatio]

lemma threeBodyGramCoefficient_one {Q : ℕ} (hQ : 2 ≤ Q) :
    threeBodyGramCoefficient Q 1 = -1 := by
  have hq : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (Q : ℝ) ≠ 0 := by linarith
  have hd : (Q : ℝ)-1 ≠ 0 := by linarith
  simp only [threeBodyGramCoefficient, fallingRatio, Nat.descFactorial_one,
    Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring

lemma threeBodyGramCoefficient_three {Q : ℕ} (hQ : 3 ≤ Q) :
    threeBodyGramCoefficient Q 3 = -1 := by
  have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : (Q : ℝ)-1 ≠ 0 := by linarith
  have h2 : (Q : ℝ)-1-1 ≠ 0 := by linarith
  have h3 : ((Q : ℝ)-1)*2-1 ≠ 0 := by linarith
  rw [threeBodyGramCoefficient, fallingRatio_eq_prod]
  norm_num [Finset.prod_range_succ, Nat.cast_sub (by omega : 2 ≤ Q),
    Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_sub (by omega : 2 ≤ 2*Q),
    Nat.cast_sub (by omega : 1 ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q-2)]
  field_simp
  ring

theorem orderedThreeWedge_null {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) (hn : z=0 ∨ z=1 ∨ z=3) :
    orderedThreeWedge hQ (coupledTensor (2*Q-2) Q z l) = 0 := by
  have hq : threeBodyGramCoefficient Q z = -1 := by
    rcases hn with rfl | rfl | rfl
    · exact threeBodyGramCoefficient_zero Q
    · exact threeBodyGramCoefficient_one hQ
    · exact threeBodyGramCoefficient_three hz
  apply dotProduct_self_eq_zero.mp
  rw [transposeMap_adjoint]
  change dotProduct (coupledTensor (2*Q-2) Q z l)
    (orderedThreeGram hQ (coupledTensor (2*Q-2) Q z l)) = 0
  rw [orderedThreeGram_eigenvalue hQ hz hl, hq]
  simp

end LaughlinGap.Spin

end

end OAI
