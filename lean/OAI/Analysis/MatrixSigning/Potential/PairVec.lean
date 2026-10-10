import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PairIndex

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

local instance : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {n : ℕ}

def pairVec (F G : E n) : E (2*n) :=
  toLp 2 (fun i => Sum.elim F G ((pairIndex n).symm i))

def fstVec (v : E (2*n)) : E n := toLp 2 (fun i => v (pairIndex n (.inl i)))
def sndVec (v : E (2*n)) : E n := toLp 2 (fun i => v (pairIndex n (.inr i)))

lemma pairVec_left (F G : E n) (i : Fin n) : pairVec F G (pairIndex n (.inl i)) = F i := by
  simp [pairVec]
lemma pairVec_right (F G : E n) (i : Fin n) : pairVec F G (pairIndex n (.inr i)) = G i := by
  simp [pairVec]
lemma pairVec_fst_snd (v : E (2*n)) : pairVec (fstVec v) (sndVec v) = v := by
  ext i
  obtain ⟨i,rfl⟩ := (pairIndex n).surjective i
  cases i <;> simp [pairVec,fstVec,sndVec]

lemma pairVec_ext {u v : E (2*n)} (hf : fstVec u = fstVec v) (hg : sndVec u = sndVec v) : u = v := by
  rw [← pairVec_fst_snd u,← pairVec_fst_snd v,hf,hg]

lemma sum_pair (f : Fin (2*n) → ℝ) :
    (∑ i, f i) = (∑ i, f (pairIndex n (.inl i)))+(∑ i, f (pairIndex n (.inr i))) := by
  rw [← (pairIndex n).sum_comp f,Fintype.sum_sum_type]

lemma offBlock_apply_left (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((offBlock A B).toEuclideanLin v) (pairIndex n (.inl i)) = B.toEuclideanLin (sndVec v) i := by
  change (∑ j,offBlock A B (pairIndex n (.inl i)) j*v j) = _
  rw [sum_pair]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_add]
  rfl

lemma offBlock_apply_right (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((offBlock A B).toEuclideanLin v) (pairIndex n (.inr i)) = A.toEuclideanLin (fstVec v) i := by
  change (∑ j,offBlock A B (pairIndex n (.inr i)) j*v j) = _
  rw [sum_pair]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,add_zero]
  rfl

def fstLin : E (2*n) →ₗ[ℝ] E n where
  toFun := fstVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sndLin : E (2*n) →ₗ[ℝ] E n where
  toFun := sndVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def responseLin (B : Mat n) : E (2*n) →ₗ[ℝ] E n := fstLin-B.toEuclideanLin.comp sndLin

def constraintLin (A B : Mat n) : E (2*n) →ₗ[ℝ] E n :=
  responseLin B-(A.toEuclideanLin.comp fstLin-sndLin)

lemma response_decomposition (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0) :
    v = pairVec (responseLin B v) (-responseLin B v)+(offBlock A B).toEuclideanLin v := by
  have he : fstVec v-B.toEuclideanLin (sndVec v) = A.toEuclideanLin (fstVec v)-sndVec v := by
    exact sub_eq_zero.mp hv
  ext i
  obtain ⟨i,rfl⟩ := (pairIndex n).surjective i
  cases i with
  | inl i =>
    simp only [WithLp.ofLp_add,Pi.add_apply,pairVec_left,offBlock_apply_left]
    change fstVec v i = (fstVec v i-B.toEuclideanLin (sndVec v) i)+B.toEuclideanLin (sndVec v) i
    ring
  | inr i =>
    simp only [WithLp.ofLp_add,Pi.add_apply,pairVec_right,offBlock_apply_right]
    rw [show responseLin B v = A.toEuclideanLin (fstVec v)-sndVec v from he]
    change sndVec v i = -(A.toEuclideanLin (fstVec v) i-sndVec v i)+A.toEuclideanLin (fstVec v) i
    ring

lemma weight_norm_sq (a : Fin (2*n) → ℝ) (ha : ∀ i, 0 < a i) (v : E (2*n)) :
    ‖weightEquiv a ha v‖^2 = ∑ i,a i*(v i)^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,weightEquiv_apply,mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sq_sqrt (ha i).le]

lemma pair_weighted_energy (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (H : E n) :
    ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (pairVec H (-H))‖^2 =
      ∑ i,(a i+b i)*(H i)^2 := by
  rw [weight_norm_sq,sum_pair,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairWeight,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,pairVec_left,pairVec_right,
    WithLp.ofLp_neg,Pi.neg_apply,neg_sq]
  ring

lemma weighted_response_bound (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0)
    (hc : ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) ((offBlock A B).toEuclideanLin v)‖^2 ≤
      (1/4 : ℝ)*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2) :
    ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B v i)^2) := by
  let : ContinuousSMul ℝ (E (2*n)) := IsBoundedSMul.continuousSMul
  let W := (weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)).toLinearMap.toContinuousLinearMap
  have hh := combined_weighted_response W (offBlock A B).toEuclideanLin.toContinuousLinearMap v
    (pairVec (responseLin B v) (-responseLin B v)) (response_decomposition A B v hv) hc
  change ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
    4*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)
      (pairVec (responseLin B v) (-responseLin B v))‖^2 at hh
  rw [pair_weighted_energy a b ha hb] at hh
  exact hh

end
end CurrentKS.Covariance

end OAI
