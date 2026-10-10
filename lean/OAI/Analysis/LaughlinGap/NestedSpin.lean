import Mathlib
import OAI.Analysis.LaughlinGap.SpinAveraging

namespace OAI

/-! Nested Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

noncomputable def onSecondMap {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ((σ × ι) → ℝ) →ₗ[ℝ] ((σ × κ) → ℝ) where
  toFun x pq := A (fun i => x (pq.1,i)) pq.2
  map_add' x y := by
    funext ⟨p,q⟩
    exact congrFun (A.map_add (fun i => x (p,i)) (fun i => y (p,i))) q
  map_smul' r x := by
    funext ⟨p,q⟩
    exact congrFun (A.map_smul r (fun i => x (p,i))) q

@[simp] lemma onSecondMap_apply {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (x : (σ × ι) → ℝ) (p : σ) (q : κ) :
    onSecondMap A x (p,q) = A (fun i => x (p,i)) q := rfl

lemma onSecondMap_onFirst {ι κ σ : Type*} [Fintype ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (B : Module.End ℝ (σ → ℝ)) (x : (σ × ι) → ℝ) :
    onSecondMap A (onFirstEnd B x) = onFirstEnd B (onSecondMap A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onSecondMap_apply, onFirstEnd_apply]
  have hfun : (fun j => A (fun i => x (j,i)) q) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) q) • (fun j => x (j,i)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (j,i))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (j,i)) p)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def LadderMap.tensorLeft {ι κ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (U : LadderSystem σ) : LadderMap (U.tensor S) (U.tensor T) where
  toLinearMap := onSecondMap A.toLinearMap
  lower x := by
    change onFirstEnd U.lower (onSecondMap A.toLinearMap x) +
      onSecondEnd T.lower (onSecondMap A.toLinearMap x) =
      onSecondMap A.toLinearMap (onFirstEnd U.lower x + onSecondEnd S.lower x)
    rw [map_add, ← onSecondMap_onFirst]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.lower (fun i => x (p,i))) q
  raise x := by
    change onFirstEnd U.raise (onSecondMap A.toLinearMap x) +
      onSecondEnd T.raise (onSecondMap A.toLinearMap x) =
      onSecondMap A.toLinearMap (onFirstEnd U.raise x + onSecondEnd S.raise x)
    rw [map_add, ← onSecondMap_onFirst]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.raise (fun i => x (p,i))) q

noncomputable def nestedSpin (n m k : ℕ) :=
  (standardLadderSystem n).tensor (tensorSpin m k)

noncomputable def nestedEmbedding {n m k r z : ℕ} (hr : r ≤ min m k)
    (hz : z ≤ min n (m+k-2*r)) :
    LadderMap (standardLadderSystem (n+(m+k-2*r)-2*z)) (nestedSpin n m k) :=
  ((coupledEmbedding hr).tensorLeft (standardLadderSystem n)).comp (coupledEmbedding hz)

noncomputable def nestedTensor (n m k r z l : ℕ) :
    (Fin (n+1) × (Fin (m+1) × Fin (k+1))) → ℝ :=
  fun a => ∑ q : Fin (m+k-2*r+1),
    coupledTensor n (m+k-2*r) z l (a.1,q) * coupledTensor m k r q.val a.2

lemma nestedEmbedding_apply {n m k r z : ℕ} (hr : r ≤ min m k)
    (hz : z ≤ min n (m+k-2*r)) (x : Fin (n+(m+k-2*r)-2*z+1) → ℝ) :
    (nestedEmbedding hr hz).toLinearMap x =
      ∑ l : Fin (n+(m+k-2*r)-2*z+1), x l • nestedTensor n m k r z l.val := by
  funext ⟨a,b⟩
  simp only [nestedEmbedding, LadderMap.comp, LinearMap.coe_comp, Function.comp_apply,
    LadderMap.tensorLeft, onSecondMap_apply, coupledEmbedding_apply, nestedTensor,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

abbrev NestedIndex (n m k : ℕ) :=
  (r : Fin (min m k+1)) × CoupledIndex n (m+k-2*r.val)

noncomputable def nestedFamily (n m k : ℕ) (a : NestedIndex n m k) :
    EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1))) :=
  WithLp.toLp 2 (nestedTensor n m k a.1.val a.2.1.val a.2.2.val)

lemma coupled_tensor_second_dot {n m k r s : ℕ} (hr : r ≤ min m k) (hs : s ≤ min m k)
    (x : (Fin (n+1) × Fin (m+k-2*r+1)) → ℝ)
    (y : (Fin (n+1) × Fin (m+k-2*s+1)) → ℝ) :
    dotProduct (onSecondMap (coupledEmbedding hr).toLinearMap x)
      (onSecondMap (coupledEmbedding hs).toLinearMap y) =
      ∑ p : Fin (n+1), ∑ l : Fin (m+k-2*r+1), ∑ t : Fin (m+k-2*s+1),
        x (p,l) * y (p,t) * if r=s ∧ l.val=t.val then (1:ℝ) else 0 := by
  rw [dotProduct, Fintype.sum_prod_type]
  simp only [onSecondMap_apply, coupledEmbedding_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hd := coupledTensor_dot (⟨⟨r,by omega⟩,l⟩ : CoupledIndex m k) ⟨⟨s,by omega⟩,t⟩
  have he : ((⟨⟨r,by omega⟩,l⟩ : CoupledIndex m k) = ⟨⟨s,by omega⟩,t⟩) ↔
      r=s ∧ l.val=t.val := by
    constructor
    · intro h
      exact ⟨congrArg (fun a : CoupledIndex m k => a.1.val) h,
        congrArg (fun a : CoupledIndex m k => a.2.val) h⟩
    · rintro ⟨rfl,hl⟩
      have : l=t := Fin.ext hl
      subst t
      rfl
  rw [if_congr he rfl rfl] at hd
  rw [← hd, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma nestedTensor_as_map {n m k r z l : ℕ} (hr : r ≤ min m k) :
    nestedTensor n m k r z l = onSecondMap (coupledEmbedding hr).toLinearMap
      (coupledTensor n (m+k-2*r) z l) := by
  funext a
  simp [nestedTensor, onSecondMap, coupledEmbedding_apply]

lemma nestedTensor_dot (n m k : ℕ) (a b : NestedIndex n m k) :
    dotProduct (nestedTensor n m k a.1.val a.2.1.val a.2.2.val)
      (nestedTensor n m k b.1.val b.2.1.val b.2.2.val) = if a=b then 1 else 0 := by
  rcases a with ⟨r,a⟩
  rcases b with ⟨s,b⟩
  rw [nestedTensor_as_map (Nat.le_of_lt_succ r.isLt),
    nestedTensor_as_map (Nat.le_of_lt_succ s.isLt), coupled_tensor_second_dot]
  by_cases he : r=s
  · subst s
    simp only [true_and, Fin.val_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    convert coupledTensor_dot a b using 1
    simp only [dotProduct, Fintype.sum_prod_type]
  · have hv : r.val ≠ s.val := by exact fun hv => he (Fin.ext hv)
    have hab : (⟨r,a⟩ : NestedIndex n m k) ≠ ⟨s,b⟩ := by
      intro h; exact he (congrArg Sigma.fst h)
    simp [hv,hab]

lemma nestedFamily_orthonormal (n m k : ℕ) : Orthonormal ℝ (nestedFamily n m k) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa only [nestedFamily, EuclideanSpace.inner_toLp_toLp, star_trivial, eq_comm] using
    nestedTensor_dot n m k b a

lemma nestedIndex_card (n m k : ℕ) :
    Fintype.card (NestedIndex n m k) = (n+1)*((m+1)*(k+1)) := by
  change Fintype.card ((r : Fin (min m k+1)) × CoupledIndex n (m+k-2*r.val)) = _
  rw [Fintype.card_sigma]
  simp only [coupledIndex_card]
  rw [← Finset.mul_sum]
  have hh := coupledIndex_card m k
  change Fintype.card ((z : Fin (min m k+1)) × Fin (m+k-2*z.val+1)) = _ at hh
  rw [Fintype.card_sigma] at hh
  simp only [Fintype.card_fin] at hh
  rw [hh]

noncomputable def nestedBasis (n m k : ℕ) : OrthonormalBasis (NestedIndex n m k) ℝ
    (EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1)))) := by
  letI : Nonempty (NestedIndex n m k) := ⟨⟨0,0,0⟩⟩
  have hc : Fintype.card (NestedIndex n m k) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1)))) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nestedIndex_card]
  let b := basisOfOrthonormalOfCardEqFinrank (nestedFamily_orthonormal n m k) hc
  exact b.toOrthonormalBasis (by simpa [b] using nestedFamily_orthonormal n m k)

@[simp] lemma nestedBasis_apply (n m k : ℕ) (a : NestedIndex n m k) :
    nestedBasis n m k a = nestedFamily n m k a := by simp [nestedBasis]

lemma nestedTensor_expansion (n m k : ℕ)
    (x : (Fin (n+1) × (Fin (m+1) × Fin (k+1))) → ℝ) :
    ∑ a : NestedIndex n m k,
      dotProduct (nestedTensor n m k a.1.val a.2.1.val a.2.2.val) x •
        nestedTensor n m k a.1.val a.2.1.val a.2.2.val = x := by
  funext p
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1))) => y p)
    ((nestedBasis n m k).sum_repr (WithLp.toLp 2 x))
  simpa only [OrthonormalBasis.repr_apply_apply, nestedBasis_apply, nestedFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

end LaughlinGap.Spin

end

end OAI
