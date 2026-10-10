import Mathlib
import OAI.Analysis.LaughlinGap.IntertwiningSpin
import OAI.Analysis.LaughlinGap.PairSpin

namespace OAI

/-! Three Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def onFirstMap {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ((ι × σ) → ℝ) →ₗ[ℝ] ((κ × σ) → ℝ) where
  toFun x pq := A (fun i => x (i,pq.2)) pq.1
  map_add' x y := by
    funext ⟨p,q⟩
    exact congrFun (A.map_add (fun i => x (i,q)) (fun i => y (i,q))) p
  map_smul' r x := by
    funext ⟨p,q⟩
    exact congrFun (A.map_smul r (fun i => x (i,q))) p

@[simp] lemma onFirstMap_apply {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (x : (ι × σ) → ℝ) (p : κ) (q : σ) :
    onFirstMap A x (p,q) = A (fun i => x (i,q)) p := rfl

lemma onFirstMap_onSecond {ι κ σ : Type*} [Fintype ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (B : Module.End ℝ (σ → ℝ)) (x : (ι × σ) → ℝ) :
    onFirstMap A (onSecondEnd B x) = onSecondEnd B (onFirstMap A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onFirstMap_apply, onSecondEnd_apply]
  have hfun : (fun j => A (fun i => x (i,j)) p) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) p) • (fun j => x (i,j)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (i,j))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (i,j)) q)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def LadderMap.tensorRight {ι κ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (U : LadderSystem σ) : LadderMap (S.tensor U) (T.tensor U) where
  toLinearMap := onFirstMap A.toLinearMap
  lower x := by
    change onFirstEnd T.lower (onFirstMap A.toLinearMap x) +
      onSecondEnd U.lower (onFirstMap A.toLinearMap x) =
      onFirstMap A.toLinearMap (onFirstEnd S.lower x + onSecondEnd U.lower x)
    rw [map_add, ← onFirstMap_onSecond]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.lower (fun i => x (i,q))) p
  raise x := by
    change onFirstEnd T.raise (onFirstMap A.toLinearMap x) +
      onSecondEnd U.raise (onFirstMap A.toLinearMap x) =
      onFirstMap A.toLinearMap (onFirstEnd S.raise x + onSecondEnd U.raise x)
    rw [map_add, ← onFirstMap_onSecond]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.raise (fun i => x (i,q))) p

noncomputable def tripleSpin (Q : ℕ) :=
  (tensorSpin Q Q).tensor (standardLadderSystem Q)

def swap23Linear (Q : ℕ) : Module.End ℝ (((Fin (Q+1) × Fin (Q+1)) × Fin (Q+1)) → ℝ) where
  toFun x ijk := x ((ijk.1.1,ijk.2),ijk.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def swap23 (Q : ℕ) : LadderMap (tripleSpin Q) (tripleSpin Q) where
  toLinearMap := swap23Linear Q
  lower x := by
    funext ⟨⟨i,j⟩,k⟩
    change lowering Q (fun i => x ((i,k),j)) i +
      lowering Q (fun j => x ((i,k),j)) j + lowering Q (fun k => x ((i,k),j)) k =
      lowering Q (fun i => x ((i,k),j)) i +
        lowering Q (fun k => x ((i,k),j)) k + lowering Q (fun j => x ((i,k),j)) j
    ring
  raise x := by
    funext ⟨⟨i,j⟩,k⟩
    change raising Q (fun i => x ((i,k),j)) i +
      raising Q (fun j => x ((i,k),j)) j + raising Q (fun k => x ((i,k),j)) k =
      raising Q (fun i => x ((i,k),j)) i +
        raising Q (fun k => x ((i,k),j)) k + raising Q (fun j => x ((i,k),j)) j
    ring

noncomputable def pairInclusion {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (standardLadderSystem (2*Q-2)) (tensorSpin Q Q) :=
  (tensorSpin Q Q).embeddingMap
    (show (tensorSpin Q Q).weight (highestTensor Q Q 1) =
        ((2*Q-2 : ℕ) : ℝ) • highestTensor Q Q 1 by
      have h := highestTensor_weight (n := Q) (m := Q) (z := 1) (by omega : 1 ≤ min Q Q)
      simpa only [mul_one, ← two_mul] using h)
    (highestTensor_raise (by omega : 1 ≤ min Q Q))

lemma pairInclusion_apply {Q : ℕ} (hQ : 2 ≤ Q) (a : Fin (2*Q-2+1) → ℝ) :
    (pairInclusion hQ).toLinearMap a =
      ∑ p : Fin (2*Q-2+1), a p • physicalPairTensor Q p.val := by
  simp only [pairInclusion, LadderSystem.embeddingMap, LadderSystem.embedding_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ p.isLt),
    coupledTensor_eq_normalized (by omega : 1 ≤ min Q Q) (by omega : p.val ≤ Q+Q-2*1)]
  congr 2
  omega

noncomputable def pairSpectatorInclusion {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (tensorSpin (2*Q-2) Q) (tripleSpin Q) :=
  (pairInclusion hQ).tensorRight (standardLadderSystem Q)

lemma pairSpectatorInclusion_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (i j k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).toLinearMap a ((i,j),k) =
      ∑ p : Fin (2*Q-2+1), pairCoefficient Q p.val i j * a (p,k) := by
  change (pairInclusion hQ).toLinearMap (fun p => a (p,k)) (i,j) = _
  rw [pairInclusion_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, physicalPairTensor, mul_comm]

noncomputable def compressedSwap {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (tensorSpin (2*Q-2) Q) (tensorSpin (2*Q-2) Q) :=
  (pairSpectatorInclusion hQ).transpose.comp ((swap23 Q).comp (pairSpectatorInclusion hQ))

noncomputable def swapScalar (Q z : ℕ) (hQ : 2 ≤ Q) : ℝ :=
  dotProduct (highestTensor (2*Q-2) Q z)
    ((compressedSwap hQ).toLinearMap (highestTensor (2*Q-2) Q z))

theorem compressedSwap_eigenvector {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    (compressedSwap hQ).toLinearMap (coupledTensor (2*Q-2) Q z l) =
      swapScalar Q z hQ • coupledTensor (2*Q-2) Q z l := by
  exact tensorSpin_schur (by omega : z ≤ min (2*Q-2) Q) hl (compressedSwap hQ)

end LaughlinGap.Spin

end

end OAI
