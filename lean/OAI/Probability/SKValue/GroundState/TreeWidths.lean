import Mathlib
import OAI.Probability.SKValue.GroundState.BranchMeanUpper

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def auxAmplitude (n : ℕ) (q : ℝ) (l : TreeLevel) : ℝ :=
  Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)

noncomputable def auxShape (n : ℕ) (q : ℝ) : GaussianTree → CascadeShape
  | [] => []
  | l::T => (auxAmplitude n q l,l.height)::auxShape n l.endpoint T

noncomputable def resizeTree (n : ℕ) (q : ℝ) : (T : GaussianTree) → CascadeWidths (auxShape n q T) → GaussianTree
  | [],_ => []
  | l::T,w => {l with branchExcess := w.1}::resizeTree n l.endpoint T w.2

lemma resizeTree_valid (n : ℕ) {q : ℝ} {T : GaussianTree} (h : ValidTreeGrid q T)
    (w : CascadeWidths (auxShape n q T)) : ValidTreeGrid q (resizeTree n q T w) := by
  induction T generalizing q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,ih h.2 w.2⟩

lemma resizeTree_scale (n : ℕ) (q : ℝ) {a : ℝ} {T : GaussianTree} (h : TreeScale a T)
    (w : CascadeWidths (auxShape n q T)) : TreeScale a (resizeTree n q T w) := by
  induction T generalizing a q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,h.2.1,ih _ h.2.2 w.2⟩

lemma auxShape_scale (n : ℕ) (q : ℝ) {a : ℝ} {T : GaussianTree} (h : TreeScale a T) :
    CascadeScale a (auxShape n q T) := by
  induction T generalizing a q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,h.2.1,ih _ h.2.2⟩

lemma resizeTree_profile (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    fieldProfile q (resizeTree n q T w)=fieldProfile q T := by
  induction T generalizing q with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,fieldProfile,ih]

lemma resizeTree_gumbelMoment (n : ℕ) (q a : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    gumbelTreeMoment a (resizeTree n q T w)=gumbelTreeMoment a T := by
  induction T generalizing q a with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,gumbelTreeMoment,ih]

lemma resizeTree_gumbelMean (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    gumbelTreeMean (resizeTree n q T w)=gumbelTreeMean T := by
  cases T with
  | nil => rfl
  | cons l T => simp only [resizeTree,gumbelTreeMean,resizeTree_gumbelMoment]

lemma resizeTree_scalarLaw (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    scalarTreeLaw (auxAmplitude n) q (resizeTree n q T w)=cascadeLaw (auxShape n q T) w := by
  induction T generalizing q with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,scalarTreeLaw,auxShape,cascadeLaw,ih,auxAmplitude]

noncomputable def treeCorrection (q : ℝ) : GaussianTree → ℝ
  | [] => 0
  | l::T => l.height*(l.endpoint^2-q^2)/4+treeCorrection l.endpoint T

lemma auxAmplitude_sq (n : ℕ) {q : ℝ} {l : TreeLevel} (hq : 0 ≤ q) (hql : q ≤ l.endpoint) :
    (auxAmplitude n q l)^2=(n : ℝ)/2*(l.endpoint^2-q^2) := by
  have hl := hq.trans hql
  have hs : 0 ≤ l.endpoint^2-q^2 := by nlinarith
  rw [auxAmplitude,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hs]

lemma auxShape_moment (n : ℕ) {q a : ℝ} {T : GaussianTree} (hq : 0 ≤ q)
    (hgrid : ValidTreeGrid q T) (h : TreeScale a T) :
    cascadeMoment a (auxShape n q T)=gumbelTreeMoment a T*Real.exp (a*(n : ℝ)*treeCorrection q T) := by
  induction T generalizing q a with
  | nil => simp [auxShape,cascadeMoment,gumbelTreeMoment,treeCorrection]
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    have hs := auxAmplitude_sq n hq hgrid.1
    rw [auxShape,cascadeMoment,ih (hq.trans hgrid.1) hgrid.2 hT]
    rw [mul_pow,hs]
    have he : Real.exp (l.height^2*((n : ℝ)/2*(l.endpoint^2-q^2))/2)*
        (gumbelTreeMoment l.height T*Real.exp (l.height*(n : ℝ)*treeCorrection l.endpoint T))=
        gumbelTreeMoment l.height T*Real.exp (l.height*(n : ℝ)*treeCorrection q (l::T)) := by
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      simp only [treeCorrection]
      ring
    rw [he,Real.mul_rpow (gumbelTreeMoment_pos hT).le (Real.exp_pos _).le,←Real.exp_mul]
    have he2 : l.height*(n : ℝ)*treeCorrection q (l::T)*(a/l.height)=a*(n : ℝ)*treeCorrection q (l::T) := by
      field_simp
    rw [he2]
    simp only [gumbelTreeMoment,mul_assoc]

lemma auxShape_mean (n : ℕ) {q : ℝ} {T : GaussianTree} (hq : 0 ≤ q)
    (hgrid : ValidTreeGrid q T) (h : TreeScale 0 T) :
    cascadeMean (auxShape n q T)=gumbelTreeMean T+(n : ℝ)*treeCorrection q T := by
  cases T with
  | nil => simp [auxShape,cascadeMean,gumbelTreeMean,treeCorrection]
  | cons l T =>
    obtain ⟨_,hm,hT⟩ := h
    have hs := auxAmplitude_sq n hq hgrid.1
    rw [auxShape,cascadeMean,auxShape_moment n (hq.trans hgrid.1) hgrid.2 hT]
    rw [Real.log_mul (Real.exp_pos _).ne' (mul_pos (gumbelTreeMoment_pos hT) (Real.exp_pos _)).ne',
      Real.log_exp,Real.log_mul (gumbelTreeMoment_pos hT).ne' (Real.exp_pos _).ne',Real.log_exp]
    rw [mul_pow,hs]
    simp only [gumbelTreeMean,treeCorrection]
    field_simp
    ring

end SKValueG

end

end OAI
