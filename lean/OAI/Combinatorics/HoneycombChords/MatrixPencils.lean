import Mathlib

namespace OAI

/-! Congruence normal forms and Schur bounds for positive real matrix pencils. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Polynomial
open scoped MatrixOrder
lemma hermitian_det_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (t : ℝ) :
    (A-t • 1).det=∏ i,(hA.eigenvalues i-t) := by
  have h:=congrArg (Polynomial.eval t) hA.charpoly_eq
  rw [Matrix.eval_charpoly] at h
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,RCLike.ofReal_real_eq_id,id_eq] at h
  have hm : (Matrix.scalar (Fin n) t-A)=(-1:ℝ) • (A-t • 1) := by
    have hs : Matrix.scalar (Fin n) t=t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.scalar_apply,Matrix.diagonal,Matrix.smul_apply,hij]
    rw [hs]
    module
  rw [hm,Matrix.det_smul,Fintype.card_fin] at h
  have hp : (∏ i : Fin n,(t-hA.eigenvalues i))=(-1:ℝ)^n*(∏ i : Fin n,(hA.eigenvalues i-t)) := by
    simp_rw [show ∀ i : Fin n,t-hA.eigenvalues i=(-1:ℝ)*(hA.eigenvalues i-t) from fun i=>by ring]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [hp] at h
  exact mul_left_cancel₀ (by exact pow_ne_zero _ (by norm_num) : (-1:ℝ)^n≠0) h

theorem positive_gram_pencil_real_factorization {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosDef) :
    ∃ e : Fin n → ℝ,∀ t : ℝ,(A-t • B).det=B.det*∏ i,(e i-t) := by
  classical
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  have hdR : IsUnit R.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdB:=hB.det_pos
    rw [hR,Matrix.det_mul] at hdB
    change 0<(R.conjTranspose).det*R.det at hdB
    rw [hz,mul_zero] at hdB
    exact lt_irrefl _ hdB
  have hRR : R*R⁻¹=1 := Matrix.mul_nonsing_inv R hdR
  have hRR' : R⁻¹*R=1 := Matrix.nonsing_inv_mul R hdR
  let C : Matrix (Fin n) (Fin n) ℝ := R⁻¹ᴴ*A*R⁻¹
  have hC : C.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ hA
  refine ⟨hC.eigenvalues,fun t=>?_⟩
  have he : A-t • B=Rᴴ*(C-t • 1)*R := by
    have hleft : Rᴴ*R⁻¹ᴴ=1 := by rw [←Matrix.conjTranspose_mul,hRR',Matrix.conjTranspose_one]
    dsimp [C]
    rw [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one]
    rw [←mul_assoc Rᴴ,←mul_assoc Rᴴ,hleft,one_mul,mul_assoc,hRR',mul_one]
    rw [hR]
    rfl
  rw [he,Matrix.det_mul,Matrix.det_mul,hermitian_det_shift _ hC]
  have hbdet : B.det=Rᴴ.det*R.det := by rw [hR,Matrix.det_mul];rfl
  rw [hbdet]
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
open scoped MatrixOrder

theorem positive_pencil_normal_form {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosDef) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
      IsUnit P.det ∧ Pᴴ*B*P=1 ∧ Pᴴ*A*P=diagonal e := by
  classical
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  have hdR : IsUnit R.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdB:=hB.det_pos
    rw [hR,Matrix.det_mul] at hdB
    change 0<(R.conjTranspose).det*R.det at hdB
    rw [hz,mul_zero] at hdB
    exact lt_irrefl _ hdB
  have hRR : R*R⁻¹=1 := Matrix.mul_nonsing_inv R hdR
  let C : Matrix (Fin n) (Fin n) ℝ := R⁻¹ᴴ*A*R⁻¹
  have hC : C.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ hA
  let U : Matrix (Fin n) (Fin n) ℝ := hC.eigenvectorUnitary
  have hU : Uᴴ*U=1 := Unitary.coe_star_mul_self hC.eigenvectorUnitary
  have hdiag : Uᴴ*C*U=diagonal hC.eigenvalues := by
    have h:=hC.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [U,Unitary.conjStarAlgAut_star_apply,RCLike.ofReal_real_eq_id,Function.id_comp,Matrix.star_eq_conjTranspose] using h
  refine ⟨R⁻¹*U,hC.eigenvalues,?_,?_,?_⟩
  · rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det R hdR).mul (isUnit_iff_ne_zero.mpr (by
      intro hz
      have h:=congrArg Matrix.det hU
      rw [Matrix.det_mul,hz,mul_zero,Matrix.det_one] at h
      exact zero_ne_one h))
  · rw [Matrix.conjTranspose_mul,hR]
    change Uᴴ*R⁻¹ᴴ*(Rᴴ*R)*(R⁻¹*U)=1
    have ht : R⁻¹ᴴ*Rᴴ=1 := by rw [←Matrix.conjTranspose_mul,hRR,Matrix.conjTranspose_one]
    calc
      _=Uᴴ*(R⁻¹ᴴ*Rᴴ)*(R*R⁻¹)*U := by noncomm_ring
      _=1 := by rw [ht,hRR,mul_one,mul_one,hU]
  · rw [Matrix.conjTranspose_mul]
    calc
      _=Uᴴ*C*U := by dsimp [C];noncomm_ring
      _=diagonal hC.eigenvalues := hdiag
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset
/-- The affine oblique Schur complement after diagonalizing the shared
positive symmetric pencil. -/
noncomputable def affineSchur {n : ℕ} (e a b c d : Fin n → ℝ) (D E u : ℝ) : ℝ :=
  D+u*E-∑ i,(a i+u*b i)*(c i+u*d i)/(e i+u)
lemma affineSchur_decomposition {n : ℕ} (e a b c d : Fin n → ℝ) (D E u : ℝ)
    (he : ∀ i,e i≠0) (heu : ∀ i,e i+u≠0) :
    affineSchur e a b c d D E u=affineSchur e a b c d D E 0+
      u*(E-∑ i,b i*d i)+∑ i,(a i-e i*b i)*(c i-e i*d i)*u/(e i*(e i+u)) := by
  have hf (i : Fin n) : (a i+u*b i)*(c i+u*d i)/(e i+u)=
      a i*c i/e i+u*(b i*d i)-(a i-e i*b i)*(c i-e i*d i)*u/(e i*(e i+u)) := by
    field_simp [he i,heu i]
    ring
  simp_rw [affineSchur,hf,sum_sub_distrib,sum_add_distrib,←mul_sum]
  simp only [zero_mul,add_zero]
  ring
/-- A positive constant, nonnegative linear term and positive Stieltjes
residues give exactly the bounded-factor comparison needed in the first
oblique chain. -/
theorem affineSchur_ratio_bounds {n : ℕ} (e a b c d : Fin n → ℝ) (D E : ℝ)
    (he : ∀ i,0<e i) (hres : ∀ i,0 ≤ (a i-e i*b i)*(c i-e i*d i))
    (hzero : 0<affineSchur e a b c d D E 0) (hlin : 0 ≤ E-∑ i,b i*d i)
    {u v : ℝ} (hu : 0<u) (huv : u ≤ v) :
    u/v ≤ affineSchur e a b c d D E u/affineSchur e a b c d D E v ∧
      affineSchur e a b c d D E u/affineSchur e a b c d D E v ≤ 1 := by
  have hv : 0<v := hu.trans_le huv
  let f:=affineSchur e a b c d D E
  let R : Fin n → ℝ := fun i=>(a i-e i*b i)*(c i-e i*d i)
  let B:=E-∑ i,b i*d i
  have hf {t : ℝ} (ht : 0<t) : f t=f 0+t*B+∑ i,R i*t/(e i*(e i+t)) :=
    affineSchur_decomposition e a b c d D E t (fun i=>(he i).ne') (fun i=>(add_pos (he i) ht).ne')
  have hpos {t : ℝ} (ht : 0<t) : 0<f t := by
    rw [hf ht]
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hzero (mul_nonneg ht.le hlin))
      (sum_nonneg (fun i _=>div_nonneg (mul_nonneg (hres i) ht.le) (mul_nonneg (he i).le (add_nonneg (he i).le ht.le))))
  have hmono : f u ≤ f v := by
    rw [hf hu,hf hv]
    apply add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right huv hlin))
    apply sum_le_sum
    intro i _
    have hfrac : u/(e i+u) ≤ v/(e i+v) := by
      rw [div_le_div_iff₀ (add_pos (he i) hu) (add_pos (he i) hv)]
      nlinarith [mul_nonneg (he i).le (sub_nonneg.mpr huv)]
    have hh:=mul_le_mul_of_nonneg_left hfrac (div_nonneg (hres i) (he i).le)
    convert hh using 1 <;> dsimp [R] <;> field_simp [(he i).ne',(add_pos (he i) hu).ne',(add_pos (he i) hv).ne']
  have hquot : f v/v ≤ f u/u := by
    have hdiv {t : ℝ} (ht : 0<t) : f t/t=f 0/t+B+∑ i,R i/(e i*(e i+t)) := by
      rw [hf ht,add_div,add_div,mul_div_cancel_left₀ _ ht.ne',sum_div]
      congr 1
      apply sum_congr rfl
      intro i _
      field_simp
    rw [hdiv hv,hdiv hu]
    apply add_le_add (add_le_add (div_le_div_of_nonneg_left hzero.le hu huv) le_rfl)
    apply sum_le_sum
    intro i _
    apply div_le_div_of_nonneg_left (hres i) (mul_pos (he i) (add_pos (he i) hu))
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl huv) (he i).le
  refine ⟨?_, (div_le_one (hpos hv)).mpr hmono⟩
  rw [div_le_div_iff₀ hv (hpos hv)]
  have h:= (div_le_div_iff₀ hv hu).mp hquot
  nlinarith only [h]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def blockBorder {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ) (d : ℝ) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks A (Matrix.of fun i _=>b i) (Matrix.of fun _ j=>c j) (Matrix.of fun _ _=>d)
lemma blockBorder_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (d : ℝ)
    (hA : IsUnit A.det) :
    (blockBorder A b c d).det=A.det*(d-c ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  let := Matrix.invertibleOfIsUnitDet A hA
  rw [blockBorder,Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,Matrix.det_fin_one]
  congr 1
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.of_apply,dotProduct,mulVec]
  congr 1
  simp_rw [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring
lemma blockBorder_diagonal_det {n : ℕ} (e b c : Fin n → ℝ) (d : ℝ)
    (he : ∀ i,e i≠0) :
    (blockBorder (diagonal e) b c d).det=(∏ i,e i)*(d-∑ i,c i*b i/e i) := by
  have hunit : IsUnit (diagonal e).det := isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_diagonal] using prod_ne_zero_iff.mpr (fun i _=>he i))
  rw [blockBorder_det _ _ _ _ hunit,Matrix.det_diagonal]
  have hinv : (diagonal e)⁻¹=diagonal (fun i=>(e i)⁻¹) := by
    exact Matrix.inv_eq_left_inv (by rw [Matrix.diagonal_mul_diagonal];simp [he])
  rw [hinv]
  congr 2
  dsimp only [dotProduct]
  apply sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  simp only [div_eq_mul_inv]
  ring
lemma blockBorder_affine_schur {n : ℕ} (e a b c d : Fin n → ℝ) (D E u : ℝ)
    (he : ∀ i,e i+u≠0) :
    (blockBorder (diagonal (fun i=>e i+u)) (fun i=>a i+u*b i) (fun i=>c i+u*d i) (D+u*E)).det=
      (∏ i,(e i+u))*affineSchur e a b c d D E u := by
  rw [blockBorder_diagonal_det _ _ _ _ he]
  congr 1
  dsimp [affineSchur]
  congr 1
  apply sum_congr rfl
  intro i _
  ring
/-- Extension of the corner change of basis to the actual bordered pencil. -/
noncomputable def extendCorner {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := Matrix.fromBlocks P 0 0 1
lemma extendCorner_det {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : (extendCorner P).det=P.det := by
  simp [extendCorner]
lemma blockBorder_congruence {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (d : ℝ) :
    (extendCorner P)ᴴ*blockBorder A b c d*extendCorner P=
      blockBorder (Pᴴ*A*P) (Pᴴ *ᵥ b) (c ᵥ* P) d := by
  simp only [extendCorner,blockBorder,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    add_zero,zero_add,Matrix.one_mul,Matrix.mul_one]
  congr 1
lemma blockBorder_congruence_det {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (d : ℝ) :
    (blockBorder (Pᴴ*A*P) (Pᴴ *ᵥ b) (c ᵥ* P) d).det=P.det^2*(blockBorder A b c d).det := by
  rw [←blockBorder_congruence,Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose,extendCorner_det]
  simp only [star_trivial]
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma positive_pencil_normal_form_pos {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
      IsUnit P.det ∧ Pᴴ*B*P=1 ∧ Pᴴ*A*P=diagonal e ∧ ∀ i,0<e i := by
  obtain ⟨P,e,hP,hB',hA'⟩ := positive_pencil_normal_form A B hA.isHermitian hB
  refine ⟨P,e,hP,hB',hA',?_⟩
  apply Matrix.posDef_diagonal_iff.mp
  rw [←hA']
  exact hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP))
noncomputable def normalRow {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1 ᵥ* Pᴴ
lemma normalRow_apply {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : normalRow P i j=P j i := by
  simp [normalRow,Matrix.single_vecMul,Matrix.row]
lemma normalRow_ne_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) (i : Fin n) :
    normalRow P i≠0 := by
  have hPt : IsUnit Pᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr (by simpa only [Matrix.det_conjTranspose,star_trivial] using hP)
  intro h
  have hh : (Pi.single i (1:ℝ) : Fin n → ℝ)=0 :=
    Matrix.vecMul_injective_iff_isUnit.mpr hPt (by simpa only [Matrix.zero_vecMul,normalRow] using h)
  have hhi:=congrFun hh i
  simp at hhi
lemma normalRow_kernel {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ)
    (hP : IsUnit P.det) (hB : Pᴴ*B*P=1) (hA : Pᴴ*A*P=diagonal e) (i : Fin n) :
    normalRow P i ᵥ* (A-e i • B)=0 := by
  apply Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP)
  change (normalRow P i ᵥ* (A-e i • B)) ᵥ* P = 0 ᵥ* P
  rw [Matrix.zero_vecMul]
  dsimp only [normalRow]
  rw [Matrix.vecMul_vecMul,Matrix.vecMul_vecMul]
  have hm : Pᴴ*(A-e i • B)*P=diagonal e-e i • (1:Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.mul_sub,Matrix.mul_smul,Matrix.sub_mul,Matrix.smul_mul,hA,hB]
  rw [←Matrix.mul_assoc,hm,Matrix.vecMul_sub,Matrix.vecMul_smul,Matrix.vecMul_one]
  rw [Matrix.single_vecMul,one_smul,Matrix.row_diagonal]
  ext j
  by_cases h : j=i
  · subst j; simp
  · simp [h]
lemma normalRow_dot {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (b : Fin n → ℝ) :
    (Pᴴ *ᵥ b) i=normalRow P i ⬝ᵥ b := by
  simp [Matrix.mulVec,dotProduct,normalRow_apply,Matrix.conjTranspose_apply]
lemma vecMul_normalRow {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (b : Fin n → ℝ) :
    (b ᵥ* P) i=normalRow P i ⬝ᵥ b := by
  simp only [Matrix.vecMul,dotProduct,normalRow_apply]
  apply sum_congr rfl
  intro j _
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma normalForm_add {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ)
    (hB : Pᴴ*B*P=1) (hA : Pᴴ*A*P=diagonal e) (u : ℝ) :
    Pᴴ*(A+u • B)*P=diagonal (fun i=>e i+u) := by
  rw [Matrix.mul_add,Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul,hA,hB]
  ext i j
  by_cases h:i=j <;> simp [h]

theorem border_pencil_ratio {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (a b c d : Fin n → ℝ) (D E : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hzero : 0<(blockBorder A a c D).det) (hlead : 0<(blockBorder B b d E).det)
    (hres : ∀ r : ℝ,∀ x : Fin n → ℝ,x≠0 → x ᵥ* (A-r • B)=0 →
      0 ≤ (x ⬝ᵥ a-r*(x ⬝ᵥ b))*(x ⬝ᵥ c-r*(x ⬝ᵥ d)))
    {u v : ℝ} (hu : 0<u) (huv : u ≤ v) :
    let K:=fun t : ℝ=>(A+t • B).det
    let J:=fun t : ℝ=>(blockBorder (A+t • B) (a+t • b) (c+t • d) (D+t*E)).det
    u/v*(K u/K v) ≤ J u/J v ∧ J u/J v ≤ K u/K v := by
  dsimp only
  obtain ⟨P,e,hP,hPB,hPA,he⟩ := positive_pencil_normal_form_pos A B hA hB
  let aa:=Pᴴ *ᵥ a
  let bb:=Pᴴ *ᵥ b
  let cc:=c ᵥ* P
  let dd:=d ᵥ* P
  let f:=affineSchur e aa bb cc dd D E
  have hdP : P.det^2≠0 := pow_ne_zero _ (isUnit_iff_ne_zero.mp hP)
  have hpP : 0<P.det^2 := sq_pos_of_ne_zero (isUnit_iff_ne_zero.mp hP)
  have hnorm (t : ℝ) : Pᴴ*(A+t • B)*P=diagonal (fun i=>e i+t) := normalForm_add A B P e hPB hPA t
  have hK (t : ℝ) : P.det^2*(A+t • B).det=∏ i,(e i+t) := by
    have h:=congrArg Matrix.det (hnorm t)
    simpa only [Matrix.det_mul,Matrix.det_conjTranspose,star_trivial,Matrix.det_diagonal,pow_two,mul_assoc,mul_left_comm,mul_comm] using h
  have hJ (t : ℝ) (ht : 0 ≤ t) : P.det^2*(blockBorder (A+t • B) (a+t • b) (c+t • d) (D+t*E)).det=(∏ i,(e i+t))*f t := by
    rw [←blockBorder_congruence_det,hnorm]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.add_vecMul,Matrix.smul_vecMul]
    exact blockBorder_affine_schur e aa bb cc dd D E t (fun i=>(add_pos_of_pos_of_nonneg (he i) ht).ne')
  have hz : 0<f 0 := by
    have hh:=hJ 0 le_rfl
    simp only [zero_smul,add_zero,zero_mul] at hh
    exact (mul_pos_iff_of_pos_left (prod_pos (fun i _=>he i))).mp (hh ▸ mul_pos hpP hzero)
  have hlin : 0 ≤ E-∑ i,bb i*dd i := by
    have hh:=blockBorder_congruence_det B P b d E
    rw [hPB] at hh
    have hId : (1:Matrix (Fin n) (Fin n) ℝ)=diagonal (fun _=>1) := by ext i j; simp
    rw [hId,blockBorder_diagonal_det _ _ _ _ (fun _=>one_ne_zero)] at hh
    simp only [prod_const_one,div_one,one_mul] at hh
    have hpos : 0<E-∑ i,dd i*bb i := by
      change 0<E-∑ i,(d ᵥ* P) i*(Pᴴ *ᵥ b) i
      rw [hh]
      exact mul_pos hpP hlead
    simpa only [mul_comm] using hpos.le
  have hr (i : Fin n) : 0 ≤ (aa i-e i*bb i)*(cc i-e i*dd i) := by
    have h:=hres (e i) (normalRow P i) (normalRow_ne_zero P hP i) (normalRow_kernel A B P e hP hPB hPA i)
    simpa only [aa,bb,cc,dd,normalRow_dot,vecMul_normalRow] using h
  have hv : 0<v := hu.trans_le huv
  have hb:=affineSchur_ratio_bounds e aa bb cc dd D E he hr hz hlin hu huv
  have hKv : 0<(A+v • B).det := by
    have hh:=hK v
    have hpos:=prod_pos (fun i (_ : i∈univ)=>add_pos (he i) hv)
    rw [←hh] at hpos
    exact (mul_pos_iff_of_pos_left hpP).mp hpos
  have hKu : 0<(A+u • B).det := by
    have hh:=hK u
    have hpos:=prod_pos (fun i (_ : i∈univ)=>add_pos (he i) hu)
    rw [←hh] at hpos
    exact (mul_pos_iff_of_pos_left hpP).mp hpos
  have hratio : (blockBorder (A+u • B) (a+u • b) (c+u • d) (D+u*E)).det /
      (blockBorder (A+v • B) (a+v • b) (c+v • d) (D+v*E)).det =
      ((A+u • B).det/(A+v • B).det)*(f u/f v) := by
    rw [←mul_div_mul_left _ _ hdP,hJ u hu.le,hJ v hv.le,mul_div_mul_comm]
    congr 1
    rw [←hK u,←hK v,mul_div_mul_left _ _ hdP]
  rw [hratio]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.1 (div_nonneg hKu.le hKv.le)
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 (div_nonneg hKu.le hKv.le)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma finBorder_submatrix {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    blockBorder (M.submatrix Fin.castSucc Fin.castSucc)
      (fun i=>M i.castSucc (Fin.last n)) (fun j=>M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n))=
      M.submatrix finSumFinEquiv finSumFinEquiv := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · have hi : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  · have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  · have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    rfl
lemma finBorder_det {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (blockBorder (M.submatrix Fin.castSucc Fin.castSucc)
      (fun i=>M i.castSucc (Fin.last n)) (fun j=>M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n))).det=M.det := by
  rw [finBorder_submatrix,Matrix.det_submatrix_equiv_self]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def lastPairing {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (x : Fin n → ℝ) : ℝ :=
  ((Fin.lastCases 0 x) ᵥ* M) (Fin.last n)
lemma lastPairing_dot {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (x : Fin n → ℝ) :
    lastPairing M x=x ⬝ᵥ (fun i=>M i.castSucc (Fin.last n)) := by
  simp only [lastPairing,Matrix.vecMul,dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,zero_mul,add_zero]
lemma lastPairing_sub_smul {n : ℕ} (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (r : ℝ) (x : Fin n → ℝ) :
    lastPairing (A-r • B) x=lastPairing A x-r*lastPairing B x := by
  simp only [lastPairing,Matrix.vecMul_sub,Matrix.vecMul_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
lemma fin_pencil_ratio {n : ℕ} (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : (A.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hB : (B.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hzero : 0<A.det) (hlead : 0<B.det)
    (hres : ∀ r : ℝ,∀ x : Fin n → ℝ,x≠0 → x ᵥ* ((A-r • B).submatrix Fin.castSucc Fin.castSucc)=0 →
      0 ≤ lastPairing (A-r • B) x*lastPairing (A-r • B).transpose x)
    {u v : ℝ} (hu : 0<u) (huv : u ≤ v) :
    u/v*(((A+u • B).submatrix Fin.castSucc Fin.castSucc).det/((A+v • B).submatrix Fin.castSucc Fin.castSucc).det) ≤
      (A+u • B).det/(A+v • B).det ∧
    (A+u • B).det/(A+v • B).det ≤
      ((A+u • B).submatrix Fin.castSucc Fin.castSucc).det/((A+v • B).submatrix Fin.castSucc Fin.castSucc).det := by
  let a:=fun i : Fin n=>A i.castSucc (Fin.last n)
  let b:=fun i : Fin n=>B i.castSucc (Fin.last n)
  let c:=fun i : Fin n=>A (Fin.last n) i.castSucc
  let d:=fun i : Fin n=>B (Fin.last n) i.castSucc
  let D:=A (Fin.last n) (Fin.last n)
  let E:=B (Fin.last n) (Fin.last n)
  have h0 : 0<(blockBorder (A.submatrix Fin.castSucc Fin.castSucc) a c D).det := by
    rw [show blockBorder (A.submatrix Fin.castSucc Fin.castSucc) a c D=
      blockBorder (A.submatrix Fin.castSucc Fin.castSucc) (fun i=>A i.castSucc (Fin.last n)) (fun j=>A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)) from rfl,finBorder_det]
    exact hzero
  have h1 : 0<(blockBorder (B.submatrix Fin.castSucc Fin.castSucc) b d E).det := by
    exact (finBorder_det B).symm ▸ hlead
  have hr (r : ℝ) (x : Fin n → ℝ) (hx : x≠0)
      (hk : x ᵥ* (A.submatrix Fin.castSucc Fin.castSucc-r • B.submatrix Fin.castSucc Fin.castSucc)=0) :
      0 ≤ (x ⬝ᵥ a-r*(x ⬝ᵥ b))*(x ⬝ᵥ c-r*(x ⬝ᵥ d)) := by
    have h:=hres r x hx hk
    rw [lastPairing_sub_smul,Matrix.transpose_sub,Matrix.transpose_smul,lastPairing_sub_smul] at h
    simpa only [lastPairing_dot,Matrix.transpose_apply,a,b,c,d] using h
  have h:=border_pencil_ratio (A.submatrix Fin.castSucc Fin.castSucc) (B.submatrix Fin.castSucc Fin.castSucc)
    a b c d D E hA hB h0 h1 hr hu huv
  have hd (t : ℝ) : (blockBorder (A.submatrix Fin.castSucc Fin.castSucc+t • B.submatrix Fin.castSucc Fin.castSucc)
      (a+t • b) (c+t • d) (D+t*E)).det=(A+t • B).det := finBorder_det (A+t • B)
  dsimp only at h
  rw [hd u,hd v] at h
  exact h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

theorem bordered_det_nonzero {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hl : ∀ a : Fin n → ℝ,a≠0 → (Fin.lastCases 0 a) ᵥ* B≠0)
    (hr : ∀ a : Fin n → ℝ,a≠0 → B *ᵥ (Fin.lastCases 0 a)≠0)
    (hA : (B.submatrix Fin.castSucc Fin.castSucc).det=0) : B.det≠0 := by
  intro hB
  obtain ⟨a,ha,haz⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hA
  obtain ⟨h,hh,hhz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB
  let v : Fin (n+1) → ℝ := (Fin.lastCases 0 a) ᵥ* B
  have hv (i : Fin n) : v i.castSucc=0 := by
    have haz' := congrFun haz i
    dsimp [v,Matrix.vecMul,dotProduct]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.lastCases_castSucc,Fin.lastCases_last,zero_mul,add_zero,Matrix.vecMul,dotProduct,Matrix.submatrix,Matrix.of_apply,Pi.zero_apply] using haz'
  have hvl : v (Fin.last n)≠0 := by
    intro hz
    apply hl a ha
    ext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact hz
    · exact hv j
  have hdot : v ⬝ᵥ h=0 := by
    dsimp [v]
    rw [←dotProduct_mulVec,hhz,dotProduct_zero]
  have hlast : h (Fin.last n)=0 := by
    rw [dotProduct,Fin.sum_univ_castSucc] at hdot
    have hsum : (∑ i : Fin n,v i.castSucc*h i.castSucc)=0 := by simp [hv]
    rw [hsum,zero_add] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left hvl
  let h' : Fin n → ℝ := fun i=>h i.castSucc
  have heq : h=Fin.lastCases 0 h' := by
    ext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa using hlast
    · simp [h']
  have hn : h'≠0 := by
    intro hz
    apply hh
    rw [heq,hz]
    ext i
    refine Fin.lastCases ?_ (fun j=>?_) i <;>simp
  exact hr h' hn (heq ▸ hhz)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
