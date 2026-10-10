import Mathlib
import OAI.Analysis.LaughlinGap.TensorSpin

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def transposeMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) := by
  classical
  exact {
    toFun := fun x i => ∑ k, A (fun j => if i=j then 1 else 0) k * x k
    map_add' := by intro x y; funext i; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro r x; funext i; simp [Finset.mul_sum, mul_left_comm] }

lemma transposeMap_adjoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (x : ι → ℝ) (y : κ → ℝ) :
    dotProduct (A x) y = dotProduct x (transposeMap A y) := by
  classical
  rw [A.pi_apply_eq_sum_univ x]
  simp only [dotProduct, transposeMap, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma eq_of_dotProduct_eq {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (h : ∀ a, dotProduct a x = dotProduct a y) : x = y := by
  classical
  funext i
  simpa [dotProduct] using h (fun j => if j=i then 1 else 0)

structure LadderMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : LadderSystem ι) (T : LadderSystem κ) extends (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  lower : ∀ x, T.lower (toLinearMap x) = toLinearMap (S.lower x)
  raise : ∀ x, T.raise (toLinearMap x) = toLinearMap (S.raise x)

namespace LadderMap
variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable {S : LadderSystem ι} {T : LadderSystem κ} {U : LadderSystem σ}

lemma weight (A : LadderMap S T) (x : ι → ℝ) :
    T.weight (A.toLinearMap x) = A.toLinearMap (S.weight x) := by
  rw [T.weight_eq, A.raise, A.lower, S.weight_eq, map_sub, A.lower, A.raise]

lemma casimir (A : LadderMap S T) (x : ι → ℝ) :
    T.casimir (A.toLinearMap x) = A.toLinearMap (S.casimir x) := by
  simp only [LadderSystem.casimir_apply, A.weight, A.lower, A.raise, map_add, map_smul]

noncomputable def comp (B : LadderMap T U) (A : LadderMap S T) : LadderMap S U where
  toLinearMap := B.toLinearMap.comp A.toLinearMap
  lower x := by simp only [LinearMap.comp_apply, B.lower, A.lower]
  raise x := by simp only [LinearMap.comp_apply, B.raise, A.raise]

noncomputable def transpose (A : LadderMap S T) : LadderMap T S where
  toLinearMap := transposeMap A.toLinearMap
  lower x := by
    apply eq_of_dotProduct_eq
    intro a
    rw [← S.raise_adjoint, ← transposeMap_adjoint, ← A.raise,
      T.raise_adjoint, transposeMap_adjoint]
  raise x := by
    apply eq_of_dotProduct_eq
    intro a
    rw [← S.adjoint, ← transposeMap_adjoint, ← A.lower,
      T.adjoint, transposeMap_adjoint]

lemma raw (A : LadderMap S T) (x : ι → ℝ) (l : ℕ) :
    T.raw (A.toLinearMap x) l = A.toLinearMap (S.raw x l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [LadderSystem.raw_succ, LadderSystem.raw_succ, ih, A.lower]

lemma normalized (A : LadderMap S T) (x : ι → ℝ) (d l : ℕ) :
    T.normalized (A.toLinearMap x) d l = A.toLinearMap (S.normalized x d l) := by
  simp only [LadderSystem.normalized, map_smul, A.raw]

end LadderMap

noncomputable def LadderSystem.embeddingMap {ι : Type*} [Fintype ι]
    (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) :
    LadderMap (standardLadderSystem d) S where
  toLinearMap := S.embedding x d
  lower a := S.embedding_lower hw he a
  raise a := S.embedding_raise hw he a

noncomputable def coupledEmbedding {n m z : ℕ} (hz : z ≤ min n m) :
    LadderMap (standardLadderSystem (n+m-2*z)) (tensorSpin n m) :=
  (tensorSpin n m).embeddingMap (highestTensor_weight hz) (highestTensor_raise hz)

lemma coupledEmbedding_apply {n m z : ℕ} (hz : z ≤ min n m)
    (a : Fin (n+m-2*z+1) → ℝ) :
    (coupledEmbedding hz).toLinearMap a =
      ∑ l : Fin (n+m-2*z+1), a l • coupledTensor n m z l.val := by
  simp only [coupledEmbedding, LadderSystem.embeddingMap, LadderSystem.embedding_apply,
    coupledTensor_eq_normalized hz (Nat.le_of_lt_succ (Fin.isLt _))]

theorem coupledTensor_expansion (n m : ℕ)
    (y : (Fin (n+1) × Fin (m+1)) → ℝ) :
    (∑ i : CoupledIndex n m,
      dotProduct (coupledTensor n m i.1.val i.2.val) y •
        coupledTensor n m i.1.val i.2.val) = y := by
  funext pq
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) => x pq)
    ((coupledBasis n m).sum_repr (WithLp.toLp 2 y))
  simpa only [OrthonormalBasis.repr_apply_apply, coupledBasis_apply, coupledFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

lemma spinCasimir_injective :
    Function.Injective (fun d : ℕ => (d : ℝ)*(d+2)) := by
  intro d e h
  have hd : (0 : ℝ) ≤ d := by positivity
  have he : (0 : ℝ) ≤ e := by positivity
  have hs : 0 < (d : ℝ)+e+2 := by positivity
  have hh : ((d : ℝ)-e)*((d : ℝ)+e+2) = 0 := by nlinarith
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hs.ne')
  exact_mod_cast heq

theorem coupledHighest_eigenline {n m z : ℕ} (hz : z ≤ min n m)
    {y : (Fin (n+1) × Fin (m+1)) → ℝ}
    (hyH : (tensorSpin n m).weight y = ((n+m-2*z : ℕ) : ℝ) • y)
    (hyC : (tensorSpin n m).casimir y =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • y) :
    y = dotProduct (highestTensor n m z) y • highestTensor n m z := by
  classical
  let iz : CoupledIndex n m := ⟨⟨z,by omega⟩,0⟩
  calc
    y = ∑ i : CoupledIndex n m,
        dotProduct (coupledTensor n m i.1.val i.2.val) y •
          coupledTensor n m i.1.val i.2.val := (coupledTensor_expansion n m y).symm
    _ = dotProduct (highestTensor n m z) y • highestTensor n m z := by
      apply Finset.sum_eq_single iz
      · intro i _ hne
        obtain ⟨w,k⟩ := i
        have hw : w.val ≤ min n m := Nat.le_of_lt_succ w.isLt
        have hk : k.val ≤ n+m-2*w.val := Nat.le_of_lt_succ k.isLt
        have horth : dotProduct (coupledTensor n m w.val k.val) y = 0 := by
          by_cases hwz : w.val=z
          · have hk0 : k.val ≠ 0 := by
              intro hk0
              apply hne
              apply Sigma.ext
              · exact Fin.ext hwz
              · apply (Fin.heq_ext_iff (by dsimp [iz]; omega)).mpr
                exact hk0
            apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
              (coupledTensor_weight hw hk) hyH
            simp only [hwz]
            intro hh
            apply hk0
            have : (k.val : ℝ) = 0 := by linarith
            exact_mod_cast this
          · apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
              (coupledTensor_casimir hw hk) hyC
            intro hh
            have HD := spinCasimir_injective hh
            have := le_min_iff.mp hw
            have := le_min_iff.mp hz
            omega
        rw [horth, zero_smul]
      · simp

lemma LadderSystem.raw_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (l : ℕ) : S.raw (c • x) l = c • S.raw x l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [S.raw_succ, ih, map_smul, S.raw_succ]

lemma LadderSystem.normalized_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (d l : ℕ) :
    S.normalized (c • x) d l = c • S.normalized x d l := by
  simp only [LadderSystem.normalized, S.raw_smul, smul_comm c]

theorem tensorSpin_schur {n m z l : ℕ} (hz : z ≤ min n m) (hl : l ≤ n+m-2*z)
    (A : LadderMap (tensorSpin n m) (tensorSpin n m)) :
    A.toLinearMap (coupledTensor n m z l) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        coupledTensor n m z l := by
  have hh : A.toLinearMap (highestTensor n m z) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        highestTensor n m z := by
    apply coupledHighest_eigenline hz
    · rw [A.weight, highestTensor_weight hz, map_smul]
    · rw [A.casimir]
      have hc := coupledTensor_casimir hz (by omega : 0 ≤ n+m-2*z)
      rw [coupledTensor_zero] at hc
      rw [hc, map_smul]
  rw [coupledTensor_eq_normalized hz hl, ← A.normalized]
  conv_lhs => rw [hh, LadderSystem.normalized_smul]

end LaughlinGap.Spin

end

end OAI
