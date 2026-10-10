import OAI.InformationTheory.Entanglement.TraceNorm

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace SecretKey
variable {n : Type} [Fintype n] [DecidableEq n]

lemma psd_column_zero {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n)
    (hi : A i i = 0) : ∀ j, A j i = 0 := by
  have h := (hA.dotProduct_mulVec_zero_iff (x := Pi.single i 1)).mp (by simpa using hi)
  intro j
  simpa using congrFun h j

lemma psd_row_zero {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n)
    (hi : A i i = 0) : ∀ j, A i j = 0 := by
  intro j
  have h := congrArg star (psd_column_zero hA i hi j)
  simpa only [← hA.isHermitian.apply i j, star_zero] using h

lemma unitary_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧
      Uᴴ * A * U = diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  refine ⟨U,hU,?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  change Uᴴ * (U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ) * U = _
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

lemma commuting_normalization {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ S T : Matrix n n ℂ, S*T=1 ∧ T*S=1 ∧ Commute (Sᴴ*A*S) (Sᴴ*B*S) := by
  let H := A+B
  have hH : H.PosSemidef := hA.add hB
  obtain ⟨U,hU,hHdiag⟩ := unitary_spectral hH.isHermitian
  let a := Uᴴ*A*U
  let b := Uᴴ*B*U
  have ha : a.PosSemidef := hA.conjTranspose_mul_mul_same U
  have hb : b.PosSemidef := hB.conjTranspose_mul_mul_same U
  let eig := hH.isHermitian.eigenvalues
  have hab : a+b = diagonal (fun i => (eig i : ℂ)) := by
    rw [← hHdiag]
    simp only [H,a,b,Matrix.mul_add,Matrix.add_mul]
  have hzero (i : n) (hi : eig i = 0) : ∀ j, a i j = 0 := by
    apply psd_row_zero ha i
    have he : a i i + b i i = 0 := by
      simpa only [Matrix.add_apply, Matrix.diagonal_apply_eq, hi, Complex.ofReal_zero] using
        congrArg (fun M => M i i) hab
    exact le_antisymm (by rw [← he]; exact le_add_of_nonneg_right hb.diag_nonneg) ha.diag_nonneg
  let d : n → ℝ := fun i => if eig i = 0 then 1 else (Real.sqrt (eig i))⁻¹
  have hd (i : n) : d i ≠ 0 := by
    dsimp [d]
    split_ifs with hi
    · exact one_ne_zero
    · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hH.eigenvalues_nonneg i) (Ne.symm hi)))
  let D : Matrix n n ℂ := diagonal (fun i => (d i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => ((d i)⁻¹ : ℂ))
  have hD : Dᴴ = D := by simp [D, Matrix.diagonal_conjTranspose]
  have hDE : D*E=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs with h
    · subst j; simp [hd]
    · rfl
  have hED : E*D=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs with h
    · subst j; simp [hd]
    · rfl
  let P : Matrix n n ℂ := diagonal (fun i => if eig i = 0 then 0 else 1)
  have hsum : D*a*D+D*b*D=P := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, hab]
    simp only [D,P,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [d]
    split_ifs with hi
    · simp [hi]
    · have hs : Real.sqrt (eig i) ≠ 0 := Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne (hH.eigenvalues_nonneg i) (Ne.symm hi))
      have he : (Real.sqrt (eig i))⁻¹ * eig i * (Real.sqrt (eig i))⁻¹ = 1 := by
        field_simp
        nlinarith [Real.sq_sqrt (show 0 ≤ eig i from hH.eigenvalues_nonneg i)]
      exact_mod_cast he
  have hAP : (D*a*D)*P=D*a*D := by
    ext i j
    simp only [P,Matrix.mul_diagonal,Matrix.diagonal_mul,D]
    by_cases hj : eig j = 0
    · have hz : a i j = 0 := by
        have hc := congrArg star (hzero j hj i)
        simpa only [← ha.isHermitian.apply i j, star_zero] using hc
      simp [hj,hz]
    · simp [hj]
  have hPA : P*(D*a*D)=D*a*D := by
    ext i j
    simp only [P,Matrix.mul_diagonal,Matrix.diagonal_mul,D]
    by_cases hi : eig i = 0
    · simp [hi,hzero i hi j]
    · simp [hi]
  refine ⟨U*D,E*Uᴴ,?_,?_,?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc D E, hDE, Matrix.one_mul, unitary_reverse hU]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hED]
  · have hb' : D*b*D=P-D*a*D := by rw [← hsum]; abel
    change Commute ((U*D)ᴴ*A*(U*D)) ((U*D)ᴴ*B*(U*D))
    have heA : (U*D)ᴴ*A*(U*D)=D*a*D := by simp [a,Matrix.conjTranspose_mul,hD,Matrix.mul_assoc]
    have heB : (U*D)ᴴ*B*(U*D)=D*b*D := by simp [b,Matrix.conjTranspose_mul,hD,Matrix.mul_assoc]
    rw [heA,heB]
    change (D*a*D)*(D*b*D)=(D*b*D)*(D*a*D)
    rw [hb',Matrix.mul_sub,Matrix.sub_mul,hAP,hPA]
end SecretKey

end

end OAI
