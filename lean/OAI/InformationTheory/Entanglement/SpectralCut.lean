import OAI.InformationTheory.Entanglement.EffectNormalization

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace SecretKey
variable {n : Type} [Fintype n] [DecidableEq n]

lemma unitary_conjugate_mul {U : Matrix n n ℂ} (hU : Uᴴ*U=1) (A B : Matrix n n ℂ) :
    (Uᴴ*A*U)*(Uᴴ*B*U)=Uᴴ*(A*B)*U := by
  have hU' := unitary_reverse hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, hU',Matrix.one_mul]

lemma unitary_conjugate_cancel {U : Matrix n n ℂ} (hU : Uᴴ*U=1) (A : Matrix n n ℂ) :
    U*(Uᴴ*A*U)*Uᴴ=A := by
  calc
    U*(Uᴴ*A*U)*Uᴴ=(U*Uᴴ)*A*(U*Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [unitary_reverse hU,Matrix.one_mul,Matrix.mul_one]

lemma unitary_conjugate_restore {U : Matrix n n ℂ} (hU : Uᴴ*U=1) (A : Matrix n n ℂ) :
    Uᴴ*(U*A*Uᴴ)*U=A := by
  calc
    Uᴴ*(U*A*Uᴴ)*U=(Uᴴ*U)*A*(Uᴴ*U) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hU,Matrix.one_mul,Matrix.mul_one]

lemma spectral_cut {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : Commute A B) :
    ∃ P : Matrix n n ℂ, Pᴴ=P ∧ P*P=P ∧ Commute P A ∧ Commute P B ∧
      (P*(A-B)*P).PosSemidef ∧ ((1-P)*(B-A)*(1-P)).PosSemidef := by
  let C := A-B
  have hC : C.IsHermitian := hA.sub hB
  obtain ⟨U,hU,hdiag⟩ := unitary_spectral hC
  have hU' := unitary_reverse hU
  let eig := hC.eigenvalues
  let a := Uᴴ*A*U
  let b := Uᴴ*B*U
  let D : Matrix n n ℂ := diagonal (fun i => (eig i : ℂ))
  change Uᴴ*C*U=D at hdiag
  have hab : a-b=D := by
    rw [← hdiag]
    simp [a,b,C,Matrix.mul_sub,Matrix.sub_mul]
  have hCA : C*A=A*C := by
    dsimp [C]
    rw [Matrix.sub_mul,Matrix.mul_sub,hAB.eq]
  have hDa : D*a=a*D := by
    rw [← hab]
    change (Uᴴ*A*U-Uᴴ*B*U)*(Uᴴ*A*U)=(Uᴴ*A*U)*(Uᴴ*A*U-Uᴴ*B*U)
    rw [← Matrix.sub_mul,← Matrix.mul_sub]
    rw [unitary_conjugate_mul hU,unitary_conjugate_mul hU,hCA]
  let q : n → ℂ := fun i => if 0 ≤ eig i then 1 else 0
  let Q : Matrix n n ℂ := diagonal q
  have hQ : Qᴴ=Q := by simp [Q,q,Matrix.diagonal_conjTranspose]
  have hQQ : Q*Q=Q := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [q]
  have hezero (i j : n) (hne : (0 ≤ eig i) ≠ (0 ≤ eig j)) : a i j=0 := by
    have he := congrArg (fun M => M i j) hDa
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal] at he
    have hz : ((eig i : ℂ) - eig j)*a i j=0 := by linear_combination he
    apply (mul_eq_zero.mp hz).resolve_left
    intro hij
    apply hne
    have hh : eig i=eig j := Complex.ofReal_injective (sub_eq_zero.mp hij)
    rw [hh]
  have hQa : Q*a=a*Q := by
    ext i j
    simp only [Q,Matrix.diagonal_mul,Matrix.mul_diagonal,q]
    split_ifs with hi hj hj
    · simp
    · rw [hezero i j (by simp [hi,hj])]; simp
    · rw [hezero i j (by simp [hi,hj])]; simp
    · simp
  have hQb : Q*b=b*Q := by
    have hb : b=a-D := by rw [← hab]; abel
    rw [hb,Matrix.mul_sub,Matrix.sub_mul,hQa]
    congr 1
    simp [Q,D,Matrix.diagonal_mul_diagonal,mul_comm]
  let P := U*Q*Uᴴ
  have hP : Pᴴ=P := by simp [P,Matrix.conjTranspose_mul,hQ,Matrix.mul_assoc]
  have hP' : Uᴴ*P*U=Q := by
    dsimp [P]
    simp only [← Matrix.mul_assoc,hU,Matrix.one_mul]
    rw [Matrix.mul_assoc,hU,Matrix.mul_one]
  have hstrong (E F : Matrix n n ℂ) (he : Uᴴ*E*U=Uᴴ*F*U) : E=F := by
    have hh := congrArg (fun M => U*M*Uᴴ) he
    simpa only [unitary_conjugate_cancel hU] using hh
  have hPP : P*P=P := by
    apply hstrong
    rw [← unitary_conjugate_mul hU P P,hP',hQQ]
  have hPA : Commute P A := by
    change P*A=A*P
    apply hstrong
    rw [← unitary_conjugate_mul hU P A,← unitary_conjugate_mul hU A P,hP']
    exact hQa
  have hPB : Commute P B := by
    change P*B=B*P
    apply hstrong
    rw [← unitary_conjugate_mul hU P B,← unitary_conjugate_mul hU B P,hP']
    exact hQb
  have hRe : Uᴴ*(1-P)*U=1-Q := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hU,hP']
  have hpos : (Q*D*Q).PosSemidef := by
    simp only [Q,D,Matrix.diagonal_mul_diagonal]
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [q]
    split_ifs with hi
    · simpa using (show (0:ℂ) ≤ eig i from Complex.nonneg_iff.mpr ⟨hi,by simp⟩)
    · simp
  have hneg : ((1-Q)*(-D)*(1-Q)).PosSemidef := by
    have h1 : (1 : Matrix n n ℂ)=diagonal (fun _ => 1) := Matrix.diagonal_one.symm
    simp only [h1,Q,D,Matrix.diagonal_sub,Matrix.diagonal_neg,
      Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [q]
    split_ifs with hi
    · simp
    · simpa using (show (0:ℂ) ≤ -(eig i:ℂ) from Complex.nonneg_iff.mpr ⟨by simpa using le_of_lt (neg_pos.mpr (lt_of_not_ge hi)),by simp⟩)
  refine ⟨P,hP,hPP,hPA,hPB,?_,?_⟩
  · have hh := hpos.mul_mul_conjTranspose_same U
    convert hh using 1
    apply hstrong
    rw [← unitary_conjugate_mul hU (P*C) P,← unitary_conjugate_mul hU P C,hP',hdiag,unitary_conjugate_restore hU]
  · have hh := hneg.mul_mul_conjTranspose_same U
    convert hh using 1
    apply hstrong
    have hd : Uᴴ*(B-A)*U = -D := by rw [show B-A= -C from by dsimp [C]; abel, Matrix.mul_neg,Matrix.neg_mul,hdiag]
    rw [← unitary_conjugate_mul hU ((1-P)*(B-A)) (1-P),← unitary_conjugate_mul hU (1-P) (B-A),hRe,hd,unitary_conjugate_restore hU]
end SecretKey

end

end OAI
