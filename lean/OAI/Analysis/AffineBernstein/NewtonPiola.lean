import Mathlib
import OAI.Analysis.AffineBernstein.ParametricVariationAlgebra
import OAI.Analysis.AffineBernstein.CofactorCodazzi

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma fderiv_piMatrix_entry (A V : ι → ι → ℝ) (l m : ι) :
    fderiv ℝ (fun B : ι → ι → ℝ => Matrix.of B l m) A V = V l m := by
  change fderiv ℝ (fun B : ι → ι → ℝ => B l m) A V = V l m
  rw [fderiv_apply (by fun_prop), fderiv_apply (by fun_prop)]
  simp

lemma adjugate_linear_piola (A : ι → ι → ℝ) (V : ι → ι → ι → ℝ)
    (hV : ∀ l j m, V j l m = V m l j) (i : ι) :
    (∑ j, fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i) A (V j)) = 0 := by
  have hh (j : ι) := fderiv_adjugate_entries (fun B : ι → ι → ℝ => Matrix.of B) A
    (fun l m => by change DifferentiableAt ℝ (fun B : ι → ι → ℝ => B l m) A; fun_prop) i j (V j)
  simp only [fderiv_piMatrix_entry] at hh
  simp_rw [hh]
  exact piola_cancel (Matrix.of A) i (fun l j m => V j l m) hV

lemma piMatrix_shift_hasDerivAt (A : ι → ι → ℝ) :
    HasDerivAt (fun t : ℝ => fun l m => A l m + t * (1 : Matrix ι ι ℝ) l m)
      (fun l m => (1 : Matrix ι ι ℝ) l m) 0 := by
  apply hasDerivAt_pi.mpr
  intro l
  apply hasDerivAt_pi.mpr
  intro m
  simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const
    ((1 : Matrix ι ι ℝ) l m)).const_add (A l m)

/- The linearized Piola cancellation is the divergence identity for the
penultimate Newton tensor. -/
lemma newton_linear_piola (A : ι → ι → ℝ) (V : ι → ι → ι → ℝ)
    (hV : ∀ l j m, V j l m = V m l j) (i : ι) :
    (∑ j, fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)) A
      (V j) (fun l m => (1 : Matrix ι ι ℝ) l m)) = 0 := by
  let I : ι → ι → ℝ := fun l m => (1 : Matrix ι ι ℝ) l m
  have hz : (fun t : ℝ => ∑ j, fderiv ℝ
      (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)
      (fun l m => A l m + t * I l m) (V j)) = fun _ => 0 := by
    funext t
    exact adjugate_linear_piola _ V hV i
  have hdj (j : ι) : HasDerivAt (fun t : ℝ => fderiv ℝ
      (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)
      (fun l m => A l m + t * I l m) (V j))
      (fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)) A I (V j)) 0 := by
    let G : (ι → ι → ℝ) → ℝ := fun B => (Matrix.of B).adjugate j i
    have hs : ContDiff ℝ ∞ G := contDiff_adjugate_entry j i
    have hh : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A) A :=
      ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) A).hasFDerivAt
    have hh' : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A)
        (fun l m => A l m + (0 : ℝ) * I l m) := by
      simpa only [zero_mul, add_zero] using hh
    have hc : HasDerivAt (fun t : ℝ => fderiv ℝ G (fun l m => A l m + t * I l m))
        (fderiv ℝ (fderiv ℝ G) A I) 0 :=
      hh'.comp_hasDerivAt 0 (piMatrix_shift_hasDerivAt A)
    have hk : HasDerivAt (fun t : ℝ => fderiv ℝ G (fun l m => A l m + t * I l m) (V j))
        (fderiv ℝ (fderiv ℝ G) A I (V j) + fderiv ℝ G A 0) 0 := by
      convert hc.clm_apply (hasDerivAt_const (0 : ℝ) (V j)) using 1
      simp only [zero_mul, add_zero]
    simpa only [map_zero, add_zero] using hk
  have hd := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hdj j)).deriv
  rw [hz, deriv_const] at hd
  rw [hd]
  apply Finset.sum_congr rfl
  intro j _
  exact ((contDiff_adjugate_entry j i).contDiffAt.isSymmSndFDerivAt
    (by simp)).eq (V j) I

end AffineBernstein
end

end OAI
