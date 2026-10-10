import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedBlock

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma actionMatrix_mul (p : A → Bool) (g h : Equiv.Perm (Fin n)) :
    actionMatrix p (g*h)=actionMatrix p g*actionMatrix p h := by
  change LinearMap.toMatrix' ((tensorRep p n) (g*h))=_
  rw [map_mul]
  exact LinearMap.toMatrix'_comp _ _

lemma actionMatrix_one (p : A → Bool) : actionMatrix (n:=n) p 1=1 := by
  change LinearMap.toMatrix' ((tensorRep p n) 1)=_
  rw [map_one]
  exact LinearMap.toMatrix'_id

lemma actionMatrix_inv (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    actionMatrix p g⁻¹=(actionMatrix p g).conjTranspose := by
  calc
    _ = actionMatrix p g⁻¹*(actionMatrix p g*(actionMatrix p g).conjTranspose) := by
      rw [actionMatrix_unitary,mul_one]
    _ = _ := by rw [← mul_assoc,← actionMatrix_mul,inv_mul_cancel,actionMatrix_one,one_mul]

def signedConj (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) :=
  actionMatrix p g*M*(actionMatrix p g).conjTranspose

lemma signedConj_mul (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M L : Matrix (Fin n → A) (Fin n → A) ℂ) :
    signedConj p g (M*L)=signedConj p g M*signedConj p g L := by
  unfold signedConj
  simp only [mul_assoc,← mul_assoc (actionMatrix p g).conjTranspose (actionMatrix p g),
    actionMatrix_star_mul,one_mul]

lemma signedConj_psd (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : M.PosSemidef) :
    (signedConj p g M).PosSemidef := hM.mul_mul_conjTranspose_same _

lemma signedConj_fixed (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : M*actionMatrix p g=actionMatrix p g*M) : signedConj p g M=M := by
  unfold signedConj
  rw [← hc,mul_assoc,actionMatrix_unitary,mul_one]

lemma signedConj_commutes (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : M*actionMatrix p g=actionMatrix p g*M) (hq : M*Q=Q*M) :
    M*signedConj p g Q=signedConj p g Q*M := by
  rw [← signedConj_fixed p g M hc,← signedConj_mul,← signedConj_mul,hq]

lemma signedConj_sub_smul_sum {U : Type*} [Fintype U] (p : A → Bool) (g : Equiv.Perm (Fin n))
    (c : ℂ) (M : U → Matrix (Fin n → A) (Fin n → A) ℂ)
    (Q : Matrix (Fin n → A) (Fin n → A) ℂ) :
    signedConj p g (c • ∑u, M u-Q)=c • ∑u, signedConj p g (M u)-signedConj p g Q := by
  simp [signedConj,mul_sub,sub_mul,Matrix.mul_sum,Matrix.sum_mul]

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A B G : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def matrixSlice (M : Matrix (A×B) (A×B) ℂ) (b c : B) : Matrix A A ℂ :=
  fun a a' => M (a,b) (a',c)

omit [DecidableEq A] in
lemma matrixSlice_mul_left (M : Matrix (A×B) (A×B) ℂ) (T : Matrix A A ℂ) (b c : B) :
    matrixSlice ((T ⊗ₖ (1 : Matrix B B ℂ))*M) b c = T*matrixSlice M b c := by
  ext a a'
  simp [matrixSlice,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]

omit [DecidableEq A] in
lemma matrixSlice_mul_right (M : Matrix (A×B) (A×B) ℂ) (T : Matrix A A ℂ) (b c : B) :
    matrixSlice (M*(T ⊗ₖ (1 : Matrix B B ℂ))) b c = matrixSlice M b c*T := by
  ext a a'
  simp [matrixSlice,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite]

omit [DecidableEq A] in
theorem kronecker_centrality (T : G → Matrix A A ℂ) (P : Matrix A A ℂ)
    (hP : ∀ X : Matrix A A ℂ, (∀ g, X*T g=T g*X) → X*P=P*X)
    (M : Matrix (A×B) (A×B) ℂ)
    (hM : ∀ g, M*(T g ⊗ₖ (1 : Matrix B B ℂ))=(T g ⊗ₖ (1 : Matrix B B ℂ))*M) :
    M*(P ⊗ₖ (1 : Matrix B B ℂ))=(P ⊗ₖ (1 : Matrix B B ℂ))*M := by
  ext ⟨a,b⟩ ⟨a',c⟩
  have hc : ∀ g, matrixSlice M b c*T g=T g*matrixSlice M b c := by
    intro g
    have hh := congrArg (fun X => matrixSlice X b c) (hM g)
    simpa only [matrixSlice_mul_left,matrixSlice_mul_right] using hh
  have hh := hP (matrixSlice M b c) hc
  have he : matrixSlice (M*(P ⊗ₖ (1 : Matrix B B ℂ))) b c =
      matrixSlice ((P ⊗ₖ (1 : Matrix B B ℂ))*M) b c := by
    simpa only [matrixSlice_mul_left,matrixSlice_mul_right] using hh
  exact congrFun (congrFun he a) a'

end BinaryCoordinateSweeps.Density

end

end OAI
