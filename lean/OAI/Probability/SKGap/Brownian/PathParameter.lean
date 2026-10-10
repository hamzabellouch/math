import Mathlib
import OAI.Probability.SKGap.Brownian.PathCutoff
import OAI.Probability.SKGap.Localization.RealParameterIncrement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

lemma sqrt_parameter_holder {a b δ : ℝ} (ha : 0≤a) (hb : 0≤b) (hδ : 0≤δ)
    (hab : |a-b|≤δ) : |sqrt a-sqrt b|≤ sqrt δ := by
  have ha2 := sq_sqrt ha
  have hb2 := sq_sqrt hb
  have hd2 := sq_sqrt hδ
  rcases le_total a b with hab'|hba
  · have hxy := sqrt_le_sqrt hab'
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg a)
    have hbd : b-a≤δ := by linarith [neg_le_abs (a-b)]
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]
  · have hxy := sqrt_le_sqrt hba
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg b)
    have had : a-b≤δ := (le_abs_self _).trans hab
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma pathDiagonal_parameter {a b : ι→ℝ} {δ : ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i)
    (hδ : 0≤δ) (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathDiagonal a 1-pathDiagonal b 1)≤ sqrt δ := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (sqrt_nonneg _) (fun i=>sqrt_parameter_holder (ha i) (hb i) hδ (hab i))

omit [DecidableEq ι] in
lemma mean_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (_hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    |(j/(Fintype.card ι:ℝ))*(∑ i,a i)-(j/(Fintype.card ι:ℝ))*(∑ i,b i)|≤j*δ := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (div_nonneg hj hn.le)]
  have hh : |∑ i,(a i-b i)|≤(Fintype.card ι:ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hab i)
  apply (mul_le_mul_of_nonneg_left hh (div_nonneg hj hn.le)).trans_eq
  field_simp

lemma pathShift_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)-
      pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))≤j*δ := by
  simp only [pathShift,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (mul_nonneg hj hδ) (fun _=>mean_parameter hj hδ hab)
end SKGap
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma spectralShift_difference (D D' C C' : Matrix ι ι ℂ) : (1+D*C*D)-(1+D'*C'*D')=(D-D')*C*D+D'*(C-C')*D+D'*C'*(D-D') := by noncomm_ring

lemma complex_product_bound (M N : Matrix ι ι ℂ) {x y : ℝ} (hx : 0≤x)
    (hM : opNorm M≤x) (hN : opNorm N≤y) : opNorm (M*N)≤x*y :=
  (opNorm_mul M N).trans (mul_le_mul hM hN (opNorm_nonneg N) hx)

lemma complex_triple_bound (M N P : Matrix ι ι ℂ) {x y z : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hM : opNorm M≤x) (hN : opNorm N≤y) (hP : opNorm P≤z) :
    opNorm (M*N*P)≤x*y*z :=
  complex_product_bound (M*N) P (mul_nonneg hx hy) (complex_product_bound M N hx hM hN) hP

lemma complex_sum_three_bound (M N P : Matrix ι ι ℂ) :
    opNorm (M+N+P)≤opNorm M+opNorm N+opNorm P :=
  (opNorm_add (M+N) P).trans (add_le_add (opNorm_add M N) le_rfl)

lemma spectralShift_parameter (D D' C C' : Matrix ι ι ℂ) {V T δ : ℝ}
    (hV : 0≤V) (hT : 0≤T) (hδ : 0≤δ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T) (hC' : opNorm C'≤T)
    (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    opNorm ((1+D*C*D)-(1+D'*C'*D'))≤(2*V*T+V^2)*δ := by
  rw [spectralShift_difference]
  have h1 := complex_triple_bound (D-D') C D hδ hT hDD hC hD
  have h2 := complex_triple_bound D' (C-C') D hV hδ hD' hCD hD
  have h3 := complex_triple_bound D' C' (D-D') hV hT hD' hC' hDD
  calc
    _ ≤ opNorm ((D-D')*C*D)+opNorm (D'*(C-C')*D)+opNorm (D'*C'*(D-D')) := complex_sum_three_bound _ _ _
    _ ≤ δ*T*V+V*δ*V+V*T*δ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma parameter_sqrt_small {δ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) : δ≤ sqrt δ := by
  have hh := sq_sqrt hδ
  nlinarith [sqrt_nonneg δ,mul_nonneg hδ (sub_nonneg.mpr hδ1)]

lemma path_parameter_factors [Nonempty ι] {a b : ι→ℝ} {j A δ : ℝ}
    (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) :
    let D := liftMatrix (pathDiagonal a 1)
    let D' := liftMatrix (pathDiagonal b 1)
    let C := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i))
    let C' := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))
    ComplexMatrix.opNorm D≤ sqrt A ∧ ComplexMatrix.opNorm D'≤ sqrt A ∧
    ComplexMatrix.opNorm C≤j*A ∧ ComplexMatrix.opNorm C'≤j*A ∧
    ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm ((1+D*C*D)-(1+D'*C'*D'))≤
      (2*sqrt A*(j*A)+(sqrt A)^2)*((1+j)*sqrt δ) := by
  intro D D' C C'
  have hz : (1:ℝ)∈Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hDa : ComplexMatrix.opNorm D≤ sqrt A := by
    simpa only [D,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA haA hz
  have hDb : ComplexMatrix.opNorm D'≤ sqrt A := by
    simpa only [D',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA hbA hz
  have hqa := diagonal_mean_bounds hj ha haA
  have hqb := diagonal_mean_bounds hj hb hbA
  have hCa : ComplexMatrix.opNorm C≤j*A := by
    simpa only [C,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqa.1).trans hqa.2
  have hCb : ComplexMatrix.opNorm C'≤j*A := by
    simpa only [C',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqb.1).trans hqb.2
  have hDD : ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ := by
    have hh : opNorm (pathDiagonal a 1-pathDiagonal b 1)≤(1+j)*sqrt δ :=
      (pathDiagonal_parameter ha hb hδ hab).trans (by nlinarith [sqrt_nonneg δ])
    simpa only [D,D',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh
  have hCC : ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ := by
    have hh := pathShift_parameter hj hδ hab
    have hh' : j*δ≤(1+j)*sqrt δ := by
      have hmul := mul_le_mul_of_nonneg_left (parameter_sqrt_small hδ hδ1) hj
      nlinarith [sqrt_nonneg δ]
    simpa only [C,C',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh.trans hh'
  exact ⟨hDa,hDb,hCa,hCb,hDD,hCC,ComplexMatrix.spectralShift_parameter _ _ _ _
    (sqrt_nonneg _) (mul_nonneg hj hA) (mul_nonneg (by linarith) (sqrt_nonneg _)) hDa hDb hCa hCb hDD hCC⟩

theorem pathK_parameter_holder [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (M N : Matrix ι ι ℝ) :
    let H := 2*sqrt A*(j*A)+(sqrt A)^2
    opNorm (pathK f R hR j a 1 M-pathK f R hR j b 1 M)≤
      ComplexMatrix.parameterKC f R (sqrt A) (j*A) H*((1+j)*sqrt δ) ∧
    ‖(pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
      (pathK f R hR j b 1 M-pathK f R hR j b 1 N)‖≤
      ComplexMatrix.parameterKM f R (sqrt A) (j*A) H*((1+j)*sqrt δ)*‖M-N‖ := by
  intro H
  obtain ⟨hDa,hDb,hCa,hCb,hDD,hCC,hBB⟩ := path_parameter_factors hj hA hδ hδ1 ha hb haA hbA hab
  let D := pathDiagonal a 1
  let D' := pathDiagonal b 1
  let C := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)
  let C' := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i)
  have hH : 0≤H := by dsimp [H];positivity
  have hh := ComplexMatrix.cutoff_parameter_constants f hR (sqrt_nonneg A) (mul_nonneg hj hA) hH
    (show 0≤(1+j)*sqrt δ by positivity)
    (1+liftMatrix D*liftMatrix C*liftMatrix D) (1+liftMatrix D'*liftMatrix C'*liftMatrix D')
    (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') hDa hDb hCa hBB hDD hCC
  constructor
  · exact (realTruncatedK_parameter f hR D D' C C' M (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans hh.1
  · exact (realTruncatedK_four_point f hR D D' C C' M N (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans
        (mul_le_mul_of_nonneg_right hh.2 (norm_nonneg _))
end SKGap
end
end

end OAI
