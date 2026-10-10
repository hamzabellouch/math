import OAI.InformationTheory.Entanglement.SpectralCut
import OAI.InformationTheory.Entanglement.CPBlocks

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m]

def quad (A : Mat n) (x : n → ℂ) : ℝ := (star x ⬝ᵥ A.mulVec x).re

lemma quad_nonneg {A : Mat n} (hA : A.PosSemidef) (x : n → ℂ) : 0 ≤ quad A x :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1
lemma quad_add (A B : Mat n) (x : n → ℂ) : quad (A+B) x=quad A x+quad B x := by
  simp [quad,Matrix.add_mulVec,dotProduct_add]
lemma quad_sub (A B : Mat n) (x : n → ℂ) : quad (A-B) x=quad A x-quad B x := by
  simp [quad,Matrix.sub_mulVec,dotProduct_sub]
lemma quad_conj (A S : Mat n) (x : n → ℂ) :
    quad (Sᴴ*A*S) x=quad A (S.mulVec x) := by
  simp only [quad,Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
lemma quad_trace (A : Mat n) (x : n → ℂ) :
    (Matrix.trace (A*projector x)).re=quad A x := by
  rw [Matrix.trace_mul_comm,trace_projector_mul]
  rfl

variable [DecidableEq n] [DecidableEq m]

lemma matrix_projection_split {A P : Mat n} (hP : P*P=P) (hPA : Commute P A) :
    A=P*A*P+(1-P)*A*(1-P) := by
  have hPAP : P*A*P=P*A := by
    rw [Matrix.mul_assoc,← hPA.eq,← Matrix.mul_assoc,hP]
  rw [hPAP]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one,hPAP]
  rw [hPA.eq]
  abel

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma sub_kronecker (A C : Mat n) (B : Mat m) :
    (A-C) ⊗ₖ B=A ⊗ₖ B-C ⊗ₖ B := by
  ext i j
  simp [Matrix.kroneckerMap_apply,sub_mul]

omit [DecidableEq n] in
lemma quad_tensor_filter (A P : Mat n) (B : Mat m) (x : n × m → ℂ) :
    quad (A ⊗ₖ B) ((P ⊗ₖ (1 : Mat m)).mulVec x)=quad ((Pᴴ*A*P) ⊗ₖ B) x := by
  rw [← quad_conj]
  simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

lemma spectral_weights (A : Fin 2 → Mat n) (B : Fin 2 → Mat m)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hcomm : Commute (A 0) (A 1)) (x : n × m → ℂ) :
    ∃ v w : n × m → ℂ, x=v+w ∧
      (∀ i j, quad (A i ⊗ₖ B j) x=quad (A i ⊗ₖ B j) v+quad (A i ⊗ₖ B j) w) ∧
      quad (A 1 ⊗ₖ B 1) v≤quad (A 0 ⊗ₖ B 1) v ∧
      quad (A 0 ⊗ₖ B 0) w≤quad (A 1 ⊗ₖ B 0) w := by
  obtain ⟨P,hPh,hPP,hPA,hPB,hpos,hneg⟩ := spectral_cut (hA 0).isHermitian (hA 1).isHermitian hcomm
  let Q : Mat n := 1-P
  have hQh : Qᴴ=Q := by simp [Q,Matrix.conjTranspose_sub,hPh]
  let v := (P ⊗ₖ (1 : Mat m)).mulVec x
  let w := (Q ⊗ₖ (1 : Mat m)).mulVec x
  have hsum : x=v+w := by
    dsimp [v,w,Q]
    rw [← Matrix.add_mulVec,← Matrix.add_kronecker]
    simp
  have hPc (i : Fin 2) : Commute P (A i) := by fin_cases i <;> assumption
  refine ⟨v,w,hsum,?_,?_,?_⟩
  · intro i j
    dsimp [v,w]
    rw [quad_tensor_filter,quad_tensor_filter,hPh,hQh,← quad_add,
      ← Matrix.add_kronecker,← matrix_projection_split hPP (hPc i)]
  · dsimp [v]
    rw [quad_tensor_filter,quad_tensor_filter,hPh]
    have h := quad_nonneg (hpos.kronecker (hB 1)) x
    rw [Matrix.mul_sub P (A 0) (A 1),Matrix.sub_mul,sub_kronecker,quad_sub] at h
    linarith
  · dsimp [w]
    rw [quad_tensor_filter,quad_tensor_filter,hQh]
    have h := quad_nonneg (hneg.kronecker (hB 0)) x
    change 0≤quad ((Q*(A 1-A 0)*Q) ⊗ₖ B 0) x at h
    rw [Matrix.mul_sub Q (A 1) (A 0),Matrix.sub_mul (Q*A 1) (Q*A 0) Q,sub_kronecker,quad_sub] at h
    linarith
end SecretKey

end

end OAI
