import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Matrix and polynomial Christoffel kernels

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def matrixChristoffel {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) : ℝ := v ⬝ᵥ (A⁻¹ *ᵥ v)
lemma matrixChristoffel_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {v : n → ℝ} (hv : v ≠ 0) : 0 < matrixChristoffel A v := by
  simpa only [matrixChristoffel,star_trivial] using hA.inv.dotProduct_mulVec_pos hv
lemma symmetric_dot_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (x y : n → ℝ) : x ⬝ᵥ (A *ᵥ y)=y ⬝ᵥ (A *ᵥ x) := by
  have hs : Aᵀ=A := by simpa using hA.eq
  rw [dotProduct_mulVec,←mulVec_transpose,hs,dotProduct_comm]
lemma matrixChristoffel_bound {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (v x : n → ℝ) :
    (x ⬝ᵥ v)^2 ≤ matrixChristoffel A v*(x ⬝ᵥ (A *ᵥ x)) := by
  by_cases hv : v=0
  · simp [hv,matrixChristoffel]
  have hK:=matrixChristoffel_pos hA hv
  let u : n → ℝ := A⁻¹ *ᵥ v
  have hAu : A *ᵥ u=v := by
    dsimp [u]
    rw [mulVec_mulVec,mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]
  have hKu : u ⬝ᵥ (A *ᵥ u)=matrixChristoffel A v := by
    rw [hAu,dotProduct_comm]
    rfl
  let t := (x ⬝ᵥ v)/matrixChristoffel A v
  have hnn:=hA.posSemidef.dotProduct_mulVec_nonneg (x-t • u)
  simp only [star_trivial,mulVec_sub,mulVec_smul,sub_dotProduct,dotProduct_sub,
    dotProduct_smul,smul_dotProduct] at hnn
  rw [symmetric_dot_mulVec hA.1 u x,hKu,hAu] at hnn
  simp only [smul_eq_mul] at hnn
  have ht : t*matrixChristoffel A v=x ⬝ᵥ v := by dsimp [t];field_simp
  nlinarith [mul_nonneg hK.le hnn]
lemma matrixChristoffel_ratio_bound {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (v x : n → ℝ) :
    (x ⬝ᵥ v)^2/(x ⬝ᵥ (A *ᵥ x)) ≤ matrixChristoffel A v := by
  by_cases hx : x=0
  · simp only [hx,zero_dotProduct,zero_pow (by omega : 2≠0),zero_div]
    by_cases hv : v=0
    · simp [hv,matrixChristoffel]
    · exact (matrixChristoffel_pos hA hv).le
  have hp : 0<x ⬝ᵥ (A *ᵥ x) := by simpa only [star_trivial] using hA.dotProduct_mulVec_pos hx
  exact (div_le_iff₀ hp).mpr (matrixChristoffel_bound hA v x)
lemma matrixChristoffel_ratio_attained {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (v : n → ℝ) :
    ∃ x : n → ℝ,(x ⬝ᵥ v)^2/(x ⬝ᵥ (A *ᵥ x))=matrixChristoffel A v := by
  by_cases hv : v=0
  · refine ⟨0,?_⟩
    simp [hv,matrixChristoffel]
  refine ⟨A⁻¹ *ᵥ v,?_⟩
  rw [mulVec_mulVec,mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec,dotProduct_comm (A⁻¹ *ᵥ v) v]
  change (matrixChristoffel A v)^2/matrixChristoffel A v=matrixChristoffel A v
  rw [pow_two,mul_div_cancel_right₀ _ (matrixChristoffel_pos hA hv).ne']
lemma matrixChristoffel_variational {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (v : n → ℝ) :
    sSup {r : ℝ | ∃ x : n → ℝ,r=(x ⬝ᵥ v)^2/(x ⬝ᵥ (A *ᵥ x))}=matrixChristoffel A v := by
  obtain ⟨x,hx⟩:=matrixChristoffel_ratio_attained hA v
  have hm : matrixChristoffel A v ∈ {r : ℝ | ∃ x : n → ℝ,r=(x ⬝ᵥ v)^2/(x ⬝ᵥ (A *ᵥ x))} := ⟨x,hx.symm⟩
  have hb : BddAbove {r : ℝ | ∃ x : n → ℝ,r=(x ⬝ᵥ v)^2/(x ⬝ᵥ (A *ᵥ x))} := by
    refine ⟨matrixChristoffel A v,?_⟩
    rintro _ ⟨y,rfl⟩
    exact matrixChristoffel_ratio_bound hA v y
  apply le_antisymm _ (le_csSup hb hm)
  apply csSup_le ⟨_,hm⟩
  rintro _ ⟨y,rfl⟩
  exact matrixChristoffel_ratio_bound hA v y
lemma matrixChristoffel_single {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i : n) : matrixChristoffel A (Pi.single i 1)=A⁻¹ i i := by
  simp [matrixChristoffel,mulVec,dotProduct,Pi.single_apply,eq_comm]
lemma matrixChristoffel_first_cofactor {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    matrixChristoffel A (Pi.single 0 1)=(A.submatrix Fin.succ Fin.succ).det/A.det := by
  rw [matrixChristoffel_single,Matrix.inv_def]
  simp only [Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv,adjugate_fin_succ_eq_det_submatrix,
    Fin.val_zero,add_zero,pow_zero,one_mul,Fin.succAbove_zero]
  ring
lemma matrixChristoffel_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℝ) (hT : IsUnit T.det) (v : n → ℝ) :
    matrixChristoffel (T*A*Tᵀ) (T *ᵥ v)=matrixChristoffel A v := by
  have hleft (u : n → ℝ) : (T *ᵥ v) ⬝ᵥ ((Tᵀ)⁻¹ *ᵥ u)=v ⬝ᵥ u := by
    rw [dotProduct_mulVec,←mulVec_transpose,←transpose_nonsing_inv,transpose_transpose,
      mulVec_mulVec,nonsing_inv_mul T hT,one_mulVec]
  unfold matrixChristoffel
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  simp only [←mulVec_mulVec]
  rw [mulVec_mulVec v T⁻¹ T,nonsing_inv_mul T hT,one_mulVec,hleft]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset MeasureTheory Filter
noncomputable def monomialVector (n : ℕ) (x : ℝ) : Fin n → ℝ := fun i=>x^i.val
noncomputable def monomialGram (n : ℕ) (w : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>∫ p in Set.Ioi (0:ℝ),(p^2)^i.val*(p^2)^j.val*w p
lemma ofFn_eval_eq_dot {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n a).eval x=a ⬝ᵥ monomialVector n x := by
  simp [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, dotProduct,monomialVector]
lemma monomial_pair_integrable (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) (i j : ℕ) :
    IntegrableOn (fun p : ℝ=>(p^2)^i*(p^2)^j*w p) (Set.Ioi 0) := by
  simpa only [←pow_mul,←pow_add] using hi (2*i+2*j)
lemma monomialGram_quadratic {n : ℕ} (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) (a : Fin n → ℝ) :
    a ⬝ᵥ ((monomialGram n w) *ᵥ a)=∫ p in Set.Ioi (0:ℝ),(Polynomial.ofFn n a).eval (p^2)^2*w p := by
  have hpair i j : IntegrableOn (fun p : ℝ=>a i*((p^2)^i.val*(p^2)^j.val*w p)*a j) (Set.Ioi 0) :=
    (monomial_pair_integrable w hi i.val j.val).const_mul (a i) |>.mul_const (a j)
  have he p : (Polynomial.ofFn n a).eval (p^2)^2*w p=
      ∑ i : Fin n,∑ j : Fin n,a i*((p^2)^i.val*(p^2)^j.val*w p)*a j := by
    rw [ofFn_eval_eq_dot,pow_two]
    simp only [dotProduct,monomialVector,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hpair i j))]
  simp_rw [integral_finsetSum _ (fun j _=>hpair _ j),integral_mul_const,integral_const_mul]
  simp [dotProduct,mulVec,monomialGram,mul_sum,mul_assoc]
lemma monomialGram_norm_integrable {n : ℕ} (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) (a : Fin n → ℝ) :
    IntegrableOn (fun p : ℝ=>(Polynomial.ofFn n a).eval (p^2)^2*w p) (Set.Ioi 0) := by
  have he p : (Polynomial.ofFn n a).eval (p^2)^2*w p=
      ∑ i : Fin n,∑ j : Fin n,a i*((p^2)^i.val*(p^2)^j.val*w p)*a j := by
    rw [ofFn_eval_eq_dot,pow_two]
    simp only [dotProduct,monomialVector,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
    (monomial_pair_integrable w hi i.val j.val).const_mul (a i) |>.mul_const (a j)))
lemma polynomial_square_eval_ae_ne_zero {P : Polynomial ℝ} (hP : P ≠ 0) :
    ∀ᵐ p : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)), P.eval (p^2) ≠ 0 := by
  have hQ : P.comp (X^2) ≠ 0 := by
    rw [ne_eq,Polynomial.comp_eq_zero_iff]
    simp only [hP,false_or,not_and_or]
    right
    intro h
    have hh:=congrArg (fun Q : Polynomial ℝ=>Q.coeff 2) h
    simp at hh
  have hf := Polynomial.finite_setOfPred_isRoot hQ
  have hzero : (volume.restrict (Set.Ioi (0:ℝ))) {p : ℝ | (P.comp (X^2)).eval p=0}=0 := hf.measure_zero _
  rw [ae_iff]
  simpa only [not_not,Polynomial.eval_comp,Polynomial.eval_pow,Polynomial.eval_X] using hzero
lemma monomialGram_posDef (n : ℕ) (w : ℝ → ℝ)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) : (monomialGram n w).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    dsimp [monomialGram,Matrix.transpose]
    congr 1
    funext p
    ring
  · intro a ha
    simp only [star_trivial,monomialGram_quadratic w hi]
    have hP : Polynomial.ofFn n a ≠ 0 := fun h=>ha ((Polynomial.injective_ofFn n) (by simpa using h))
    have hae : ∀ᵐ p : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),0<(Polynomial.ofFn n a).eval (p^2)^2*w p := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi,polynomial_square_eval_ae_ne_zero hP] with p hp hn
      exact mul_pos (sq_pos_of_ne_zero hn) (hw p hp)
    apply (integral_pos_iff_support_of_nonneg_ae (hae.mono fun _ h=>h.le) (monomialGram_norm_integrable w hi a)).mpr
    have hs : Function.support (fun p : ℝ=>(Polynomial.ofFn n a).eval (p^2)^2*w p)=ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Set.univ := by
      filter_upwards [hae] with p hp
      exact propext (iff_of_true hp.ne' trivial)
    rw [measure_congr hs]
    simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset MeasureTheory Filter
noncomputable def rootBasisMatrix (n : ℕ) (a : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i=>Fin.cases (Pi.single 0 1) (fun j=>Pi.single j.succ 1-a • Pi.single j.castSucc 1) i
lemma rootBasisMatrix_det (n : ℕ) (a : ℝ) : (rootBasisMatrix n a).det=1 := by
  have ht : (rootBasisMatrix n a).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    cases i using Fin.cases with
    | zero =>
      simp only [rootBasisMatrix,Fin.cases_zero,Pi.single_apply]
      rw [ite_eq_right (by simp only [Fin.lt_def,Fin.ext_iff,Fin.val_zero] at *; omega)]
    | succ i =>
      have h1 : i.succ ≠ j := ne_of_lt hij
      have h2 : i.castSucc ≠ j := ne_of_lt (i.castSucc_lt_succ.trans hij)
      simp [rootBasisMatrix,h1,h2]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  have hd (i : Fin (n+1)) : rootBasisMatrix n a i i=1 := by
    cases i using Fin.cases with
    | zero => simp [rootBasisMatrix]
    | succ i =>
      have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
      simp [rootBasisMatrix,hne]
  simp only [hd,prod_const_one]
lemma rootBasisMatrix_eval_zero (n : ℕ) (a x : ℝ) :
    (rootBasisMatrix n a *ᵥ monomialVector (n+1) x) 0=1 := by
  simp [rootBasisMatrix,mulVec,monomialVector,dotProduct,Pi.single_apply]
lemma rootBasisMatrix_eval_succ {n : ℕ} (a x : ℝ) (i : Fin n) :
    (rootBasisMatrix n a *ᵥ monomialVector (n+1) x) i.succ=(x-a)*x^i.val := by
  change (Pi.single i.succ 1-a • Pi.single i.castSucc 1) ⬝ᵥ monomialVector (n+1) x=_
  rw [sub_dotProduct,smul_dotProduct]
  simp only [single_dotProduct,one_mul,monomialVector,Fin.val_succ,Fin.val_castSucc,smul_eq_mul,pow_succ]
  ring
lemma rootBasisMatrix_eval_self (n : ℕ) (a : ℝ) :
    rootBasisMatrix n a *ᵥ monomialVector (n+1) a=Pi.single 0 1 := by
  ext i
  cases i using Fin.cases with
  | zero => simp [rootBasisMatrix_eval_zero]
  | succ i => simp [rootBasisMatrix_eval_succ]
lemma monomialGram_congruence_entry {n : ℕ} (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0))
    (T : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (T*monomialGram n w*Tᵀ) i j=
      ∫ p in Set.Ioi (0:ℝ),(T *ᵥ monomialVector n (p^2)) i*(T *ᵥ monomialVector n (p^2)) j*w p := by
  have hpair k l : IntegrableOn (fun p : ℝ=>T i k*((p^2)^k.val*(p^2)^l.val*w p)*T j l) (Set.Ioi 0) :=
    (monomial_pair_integrable w hi k.val l.val).const_mul (T i k) |>.mul_const (T j l)
  have he p : (T *ᵥ monomialVector n (p^2)) i*(T *ᵥ monomialVector n (p^2)) j*w p=
      ∑ k : Fin n,∑ l : Fin n,T i k*((p^2)^k.val*(p^2)^l.val*w p)*T j l := by
    simp only [mulVec,dotProduct,monomialVector,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _=>integrable_finsetSum _ (fun l _=>hpair k l))]
  simp_rw [integral_finsetSum _ (fun l _=>hpair _ l),integral_mul_const,integral_const_mul]
  simp only [Matrix.mul_apply,transpose_apply,monomialGram,sum_mul]
  rw [sum_comm]
lemma rootBasisGram_minor (n : ℕ) (a : ℝ) (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    (rootBasisMatrix n a*monomialGram (n+1) w*(rootBasisMatrix n a)ᵀ).submatrix Fin.succ Fin.succ=
      monomialGram n (fun p=>(p^2-a)^2*w p) := by
  ext i j
  rw [Matrix.submatrix_apply,monomialGram_congruence_entry w hi]
  simp_rw [rootBasisMatrix_eval_succ]
  apply integral_congr_ae
  filter_upwards with p
  ring
/-- Gram cofactor identity used in the manuscript's polynomial comparison. -/
theorem polynomial_compression_cofactor (n : ℕ) (a : ℝ) (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    (monomialGram n (fun p=>(p^2-a)^2*w p)).det/(monomialGram (n+1) w).det=
      matrixChristoffel (monomialGram (n+1) w) (monomialVector (n+1) a) := by
  have hdet : IsUnit (rootBasisMatrix n a).det := by rw [rootBasisMatrix_det];exact isUnit_one
  have h:=matrixChristoffel_congruence (monomialGram (n+1) w) (rootBasisMatrix n a) hdet (monomialVector (n+1) a)
  rw [rootBasisMatrix_eval_self,matrixChristoffel_first_cofactor,rootBasisGram_minor n a w hi,
    det_mul,det_mul,det_transpose,rootBasisMatrix_det,one_mul,mul_one] at h
  exact h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset MeasureTheory Filter
noncomputable def weightedPolynomialNorm (w : ℝ → ℝ) (P : Polynomial ℝ) : ℝ :=
  ∫ p in Set.Ioi (0:ℝ), P.eval (p^2)^2*w p
noncomputable def weightedPolynomialChristoffel (w : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧ r=P.eval x^2/weightedPolynomialNorm w P}
lemma weightedPolynomialNorm_integrable (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) (P : Polynomial ℝ) :
    IntegrableOn (fun p : ℝ=>P.eval (p^2)^2*w p) (Set.Ioi 0) := by
  have he := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self P.natDegree)
  rw [←he]
  exact monomialGram_norm_integrable w hi _
lemma weightedPolynomialNorm_nonneg (w : ℝ → ℝ) (hw : ∀ p,0<p → 0≤w p) (P : Polynomial ℝ) :
    0≤weightedPolynomialNorm w P := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact mul_nonneg (sq_nonneg _) (hw p hp)
lemma weightedPolynomialChristoffel_eq (n : ℕ) (x : ℝ) (w : ℝ → ℝ)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    weightedPolynomialChristoffel w n x=matrixChristoffel (monomialGram (n+1) w) (monomialVector (n+1) x) := by
  rw [←matrixChristoffel_variational (monomialGram_posDef (n+1) w hw hi)]
  unfold weightedPolynomialChristoffel
  congr 1
  ext r
  constructor
  · rintro ⟨P,hP,rfl⟩
    have he := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hP)
    refine ⟨P.toFn (n+1),?_⟩
    rw [monomialGram_quadratic w hi,he]
    rw [←ofFn_eval_eq_dot,he]
    rfl
  · rintro ⟨a,rfl⟩
    refine ⟨Polynomial.ofFn (n+1) a,Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) a),?_⟩
    rw [monomialGram_quadratic w hi,ofFn_eval_eq_dot]
    rfl
lemma weightedPolynomial_ratio_bound (n : ℕ) (x : ℝ) (w : ℝ → ℝ)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0))
    (P : Polynomial ℝ) (hP : P.natDegree≤n) :
    P.eval x^2/weightedPolynomialNorm w P≤weightedPolynomialChristoffel w n x := by
  rw [weightedPolynomialChristoffel_eq n x w hw hi]
  have he := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hP)
  have h:=matrixChristoffel_ratio_bound (monomialGram_posDef (n+1) w hw hi) (monomialVector (n+1) x) (P.toFn (n+1))
  rw [monomialGram_quadratic w hi,←ofFn_eval_eq_dot,he] at h
  exact h
lemma weightedPolynomial_ratio_attained (n : ℕ) (x : ℝ) (w : ℝ → ℝ)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    ∃ P : Polynomial ℝ,P.natDegree≤n ∧ P.eval x^2/weightedPolynomialNorm w P=weightedPolynomialChristoffel w n x := by
  rw [weightedPolynomialChristoffel_eq n x w hw hi]
  obtain ⟨a,ha⟩:=matrixChristoffel_ratio_attained (monomialGram_posDef (n+1) w hw hi) (monomialVector (n+1) x)
  refine ⟨Polynomial.ofFn (n+1) a,Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) a),?_⟩
  rw [monomialGram_quadratic w hi,←ofFn_eval_eq_dot] at ha
  exact ha
lemma weightedPolynomialNorm_pos (w : ℝ → ℝ) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0))
    {P : Polynomial ℝ} (hP : P≠0) : 0<weightedPolynomialNorm w P := by
  have he := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self P.natDegree)
  have ha : P.toFn (P.natDegree+1)≠0 := by
    intro h
    rw [h] at he
    exact hP (by simpa using he.symm)
  have h := (monomialGram_posDef (P.natDegree+1) w hw hi).dotProduct_mulVec_pos ha
  simpa only [star_trivial,monomialGram_quadratic w hi,he,weightedPolynomialNorm] using h
lemma weightedPolynomialChristoffel_comparison (n : ℕ) (x : ℝ) {w₁ w₂ : ℝ → ℝ} {c : ℝ}
    (hc : 0<c) (hw₁ : ∀ p,0<p → 0<w₁ p) (hw₂ : ∀ p,0<p → 0<w₂ p)
    (hi₁ : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w₁ p) (Set.Ioi 0))
    (hi₂ : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w₂ p) (Set.Ioi 0))
    (h : ∀ p,0<p → c*w₁ p≤w₂ p) :
    weightedPolynomialChristoffel w₂ n x≤weightedPolynomialChristoffel w₁ n x/c := by
  obtain ⟨P,hP,hPe⟩:=weightedPolynomial_ratio_attained n x w₂ hw₂ hi₂
  rw [←hPe]
  by_cases hz : P=0
  · simp only [hz,Polynomial.eval_zero,zero_pow (by omega : 2≠0),zero_div]
    apply div_nonneg _ hc.le
    rw [weightedPolynomialChristoffel_eq n x w₁ hw₁ hi₁]
    have hv : monomialVector (n+1) x≠0 := by intro hn; have h0:=congrFun hn 0; simp [monomialVector] at h0
    exact (matrixChristoffel_pos (monomialGram_posDef (n+1) w₁ hw₁ hi₁) hv).le
  have hp₁:=weightedPolynomialNorm_pos w₁ hw₁ hi₁ hz
  have hp₂:=weightedPolynomialNorm_pos w₂ hw₂ hi₂ hz
  have hnorm : c*weightedPolynomialNorm w₁ P≤weightedPolynomialNorm w₂ P := by
    rw [weightedPolynomialNorm,←integral_const_mul]
    apply integral_mono_ae ((weightedPolynomialNorm_integrable w₁ hi₁ P).const_mul c) (weightedPolynomialNorm_integrable w₂ hi₂ P)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    nlinarith [mul_le_mul_of_nonneg_left (h p hp) (sq_nonneg (P.eval (p^2)))]
  calc
    P.eval x^2/weightedPolynomialNorm w₂ P ≤ P.eval x^2/(c*weightedPolynomialNorm w₁ P) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hc hp₁) hnorm
    _ = (P.eval x^2/weightedPolynomialNorm w₁ P)/c := by ring
    _ ≤ weightedPolynomialChristoffel w₁ n x/c := div_le_div_of_nonneg_right (weightedPolynomial_ratio_bound n x w₁ hw₁ hi₁ P hP) hc.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
