import Mathlib
import OAI.Geometry.PrescribedRicci.JetRemainder
import OAI.Geometry.PrescribedRicci.MatrixDifferentialNew
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator

namespace OAI

/-! Determinant Jet. -/

section

 

noncomputable section
open Set Finset Matrix
open scoped ContDiff Classical BigOperators Matrix.Norms.Elementwise
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} {n : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cword_finite_sum (e : ι → E) (ws : List ι) {ν : Type*} (s : Finset ν)
    (f : ν → E → ℂ) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    cword e (fun x => ∑ i ∈ s, f i x) ws = fun x => ∑ i ∈ s, cword e (f i) ws x := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e (fun x => ∑ i ∈ s, f i x) ws) = _
    rw [ih,cdir_finite_sum e a s _ (fun i hi => cword_smooth e (hf i hi) ws)]
    rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cword_const_mul (e : ι → E) (ws : List ι) (c : ℂ) (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) :
    cword e (fun x => c*f x) ws = fun x => c*cword e f ws x := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e (fun x => c*f x) ws) = _
    rw [ih]
    funext x
    unfold cdir
    rw [fderiv_const_mul ((cword_smooth e hf ws).differentiable (by simp) x)]
    rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma monoEval_single (e : ι → E) (f : Fin n → E → ℂ) (ws : List ι) (i : Fin n) (x : E) :
    monoEval e f (singleState ws i) x = cword e (f i) ws x * ∏ j ∈ Finset.univ.erase i, f j x := by
  unfold monoEval
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [singleState,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rfl

def detPrincipal (M N : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
    ∑ i, N (σ i) i * ∏ j ∈ Finset.univ.erase i, M (σ j) j

lemma detPrincipal_eq (M N : Matrix (Fin n) (Fin n) ℂ) :
    detPrincipal M N = NonlinearHessian.detDifferential M N := by
  have hp : HasDerivAt (fun t : ℂ => (M+t•N).det) (detPrincipal M N) 0 := by
    have hent (i j : Fin n) : HasDerivAt (fun t : ℂ => M i j+t*N i j) (N i j) 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).mul_const (N i j)).const_add (M i j)
    have hprod (σ : Equiv.Perm (Fin n)) :=
      HasDerivAt.finsetProd (u:=Finset.univ) (fun i _ => hent (σ i) i)
    have hs := HasDerivAt.fun_sum (u:=Finset.univ)
      (fun σ _ => hprod σ |>.const_mul (Equiv.Perm.sign σ : ℂ))
    convert! hs using 1
    · funext t
      simp only [Matrix.det_apply',Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
        Finset.prod_apply]
    · unfold detPrincipal
      simp only [zero_mul,add_zero,smul_eq_mul,mul_comm]
  have hc : HasDerivAt (fun t : ℂ => M+t•N) N 0 := by
    convert! ((hasDerivAt_id (0:ℂ)).smul_const N).const_add M using 1
    simp only [one_smul]
  have hd := (MongeAmpere.differentiable_det (M+(0:ℂ)•N)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hd' : HasDerivAt (fun t : ℂ => (M+t•N).det)
      (fderiv ℂ (fun K : Matrix (Fin n) (Fin n) ℂ => K.det) M N) 0 := by
    convert! hd using 1
    simp only [zero_smul,add_zero]
    rfl
  have hr := ((MongeAmpere.differentiable_det M).hasFDerivAt.restrictScalars ℝ).fderiv
  have hre := congrArg (fun L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ => L N) hr
  exact (hp.unique hd').trans hre.symm

def detJetRemainder (e : ι → E) (H : E → Matrix (Fin n) (Fin n) ℂ) (ws : List ι) (x : E) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
    ((monoRemainder ws).map (fun s => monoEval e (fun i x => H x (σ i) i) s x)).sum

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem cword_det_remainder (e : ι → E) (H : E → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContDiff ℝ ∞ (fun x => H x i j)) (ws : List ι) (hw : ws ≠ []) (x : E) :
    cword e (fun x => (H x).det) ws x =
      NonlinearHessian.detDifferential (H x) (fun i j => cword e (fun y => H y i j) ws x) +
        detJetRemainder e H ws x := by
  have he : (fun x => (H x).det) = (fun x => ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℂ)*∏ i, H x (σ i) i) := by
    funext x; exact Matrix.det_apply' (H x)
  rw [he,cword_finite_sum e ws _ _ (by
    intro σ _; exact contDiff_const.mul (contDiff_prod fun i _ => hH (σ i) i))]
  simp_rw [cword_const_mul e ws _ _ (contDiff_prod fun i _ => hH _ i)]
  simp_rw [cword_product_remainder e _ (fun i => hH _ i) ws hw]
  erw [← detPrincipal_eq]
  unfold detPrincipal detJetRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [monoEval_single]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem cword_det_trace (e : ι → E) (H : E → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContDiff ℝ ∞ (fun x => H x i j)) (ws : List ι) (hw : ws ≠ []) (x : E)
    (hinv : IsUnit (H x).det) :
    cword e (fun x => (H x).det) ws x =
      (H x).det * ((H x)⁻¹ * (show Matrix (Fin n) (Fin n) ℂ from fun i j => cword e (fun y => H y i j) ws x)).trace +
        detJetRemainder e H ws x := by
  rw [cword_det_remainder e H hH ws hw x]
  congr 1
  exact MongeAmpere.real_fderiv_det_apply _ _ hinv
end TameInterpolation

end
end

end OAI
