import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SchattenBounds

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma alternating_prod {R : Type*} [Monoid R] (q : ℕ) (x y : R) :
    (List.ofFn (fun i : Fin (2*q) => if i.val%2=0 then x else y)).prod=(x*y)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega]
    simp only [List.ofFn_succ,List.prod_cons,Fin.val_zero,Fin.val_succ]
    norm_num only [Nat.zero_mod,Nat.reduceMod,ite_eq_left,ite_eq_right]
    have he (i : Fin (2*q)) : (i.val+1+1)%2=i.val%2 := by omega
    simp_rw [he]
    rw [ih,pow_succ']
    exact (mul_assoc _ _ _).symm

lemma alternating_prod_real (q : ℕ) (x y : ℝ) :
    (∏i : Fin (2*q), if i.val%2=0 then x else y)=(x*y)^q := by
  rw [← List.prod_ofFn]
  exact alternating_prod q x y

lemma alternating_gram (q : ℕ) (A : M ι) :
    (List.ofFn (fun i : Fin (2*q) => if i.val%2=0 then star A else A)).prod=
      (star A*A)^q := alternating_prod q _ _

lemma mul_pow_rotate {R : Type*} [Monoid R] (q : ℕ) (x y : R) :
    (x*y)^(q+1)=x*(y*x)^q*y := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ,ih,pow_succ]; simp only [mul_assoc]

lemma matrixMoment_smul (q : ℕ) (r : ℝ) (A : M ι) :
    matrixMoment q (r • A)=r^(2*q)*matrixMoment q A := by
  unfold matrixMoment
  rw [star_smul,star_trivial,smul_mul_smul_comm,smul_pow,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [← pow_two,← pow_mul]

lemma momentRoot_pow {q : ℕ} (hq : 0 < q) (A : M ι) :
    (matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹))^(2*q)=matrixMoment q A := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (matrixMoment_nonneg q A),
    inv_mul_cancel₀ (show ((2*q:ℕ):ℝ)≠0 by positivity),Real.rpow_one]

lemma matrixMoment_of_density_sandwich_le {q : ℕ} (hq : 0<q)
    (d : ι → ℝ) (hd : ∀i, 0≤d i) (hs : ∑i, d i=1)
    (U V : M ι) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    matrixMoment q (U*diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)*V) ≤ 1 := by
  let D := diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)
  have hD : star D=D := by
    unfold D
    rw [diagPower_real d hd (by positivity)]
    exact star_diagReal _
  have hb := trace_diagonal_sandwich_pos (show 0<2*q by omega)
    (fun _ => d) (fun _ => hd) (fun _ => hs)
    (fun _ => ((2*q:ℕ):ℝ)⁻¹) (fun _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];
        exact mul_inv_cancel₀ (by positivity))
    (fun i : Fin (2*q) => if i.val%2=0 then star V else U)
    (fun i : Fin (2*q) => if i.val%2=0 then star U else V)
    (by intro i; split_ifs <;> simpa only [norm_star] using (by assumption))
    (by intro i; split_ifs <;> simpa only [norm_star] using (by assumption))
  have he : (fun i : Fin (2*q) =>
      (if i.val%2=0 then star V else U)*D*(if i.val%2=0 then star U else V))=
      fun i => if i.val%2=0 then star (U*D*V) else U*D*V := by
    funext i
    split_ifs <;> simp only [star_mul,hD,mul_assoc]
  change ‖Matrix.trace (List.ofFn (fun i : Fin (2*q) =>
    (if i.val%2=0 then star V else U)*D*(if i.val%2=0 then star U else V))).prod‖≤1 at hb
  rw [he,alternating_gram] at hb
  exact (Complex.re_le_norm _).trans hb

lemma matrixMoment_contract_left {q : ℕ} (hq : 0<q) (C A : M ι) (hC : ‖C‖≤1) :
    matrixMoment q (C*A) ≤ matrixMoment q A := by
  by_cases hz : matrixMoment q A=0
  · have ha := (matrixMoment_eq_zero_iff hq A).mp hz
    simp only [ha,mul_zero]
    exact le_rfl
  have ht := lt_of_le_of_ne (matrixMoment_nonneg q A) (Ne.symm hz)
  obtain ⟨U,V,d,hU,hV,hd,hs,he⟩ := normalized_svd hq A ht
  have hec : C*A = matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹) •
      ((C*U)*diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)*V) := by
    conv_lhs => rw [he]
    rw [mul_smul_comm]
    congr 1
    simp only [mul_assoc]
  rw [hec,matrixMoment_smul,momentRoot_pow hq A]
  exact mul_le_of_le_one_right ht.le (matrixMoment_of_density_sandwich_le hq d hd hs
    (C*U) V ((norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hC).trans hU)) hV)

lemma matrixMoment_contract_right {q : ℕ} (hq : 0<q) (A C : M ι) (hC : ‖C‖≤1) :
    matrixMoment q (A*C) ≤ matrixMoment q A := by
  rw [← matrixMoment_star q (A*C),star_mul]
  exact (matrixMoment_contract_left hq (star C) (star A) (by simpa using hC)).trans_eq
    (matrixMoment_star q A)

lemma matrixMoment_mul_left {q : ℕ} (hq : 0<q) (C A : M ι) :
    matrixMoment q (C*A) ≤ ‖C‖^(2*q)*matrixMoment q A := by
  by_cases hc : C=0
  · simp only [hc,zero_mul,norm_zero,zero_pow (by omega : 2*q≠0),
      (matrixMoment_eq_zero_iff hq (0:M ι)).mpr rfl]
    exact le_rfl
  have hn : 0<‖C‖ := norm_pos_iff.mpr hc
  have hf : ‖‖C‖⁻¹ • C‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : C=‖C‖ • (‖C‖⁻¹ • C) := by rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  conv_lhs => rw [he,smul_mul_assoc,matrixMoment_smul]
  exact mul_le_mul_of_nonneg_left (matrixMoment_contract_left hq _ A hf) (pow_nonneg hn.le _)

lemma matrixMoment_unitary_conj (q : ℕ) (U : Matrix.unitaryGroup ι ℂ) (A : M ι) :
    matrixMoment q ((U:M ι)*A*star (U:M ι))=matrixMoment q A := by
  unfold matrixMoment
  have he : star ((U:M ι)*A*star (U:M ι))*((U:M ι)*A*star (U:M ι))=
      (U:M ι)*(star A*A)*star (U:M ι) := by
    simp only [star_mul,star_star,mul_assoc,← mul_assoc (star (U:M ι)) (U:M ι),
      Unitary.coe_star_mul_self,one_mul]
  rw [he,unitary_conj_pow,trace_unitary_conj]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
