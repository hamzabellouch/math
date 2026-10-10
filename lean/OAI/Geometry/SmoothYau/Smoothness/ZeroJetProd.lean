import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {x : E}

lemma zero_jet_prod (f : ι → E → ℝ) (hf : ∀ i, HasFDerivAt (f i) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => ∏ i, f i y) (0 : E →L[ℝ] ℝ) x := by
  simpa using HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hf i)

omit [DecidableEq ι] in
lemma zero_jet_sum (f : ι → E → ℝ) (hf : ∀ i, HasFDerivAt (f i) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => ∑ i, f i y) (0 : E →L[ℝ] ℝ) x := by
  simpa using HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hf i)

lemma zero_jet_det (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => (A y).det) (0 : E →L[ℝ] ℝ) x := by
  simp only [Matrix.det_apply']
  apply zero_jet_sum
  intro σ
  simpa using (zero_jet_prod (fun i y => A y (σ i) i) (fun i => hA (σ i) i)).const_mul (Equiv.Perm.sign σ : ℝ)

lemma zero_jet_adjugate (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x) (i j : ι) :
    HasFDerivAt (fun y => (A y).adjugate i j) (0 : E →L[ℝ] ℝ) x := by
  simp only [Matrix.adjugate_apply]
  apply zero_jet_det
  intro k l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact hasFDerivAt_const _ _
  · exact hA _ _

lemma zero_jet_inverse (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) (i j : ι) :
    HasFDerivAt (fun y => (A y)⁻¹ i j) (0 : E →L[ℝ] ℝ) x := by
  have hi := (hasFDerivAt_inv hn).comp x (zero_jet_det A hA)
  have hh := hi.mul (zero_jet_adjugate A hA i j)
  convert! hh using 1
  · funext y
    simp [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  · simp

lemma zero_jet_density (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) :
    HasFDerivAt (fun y => Real.sqrt (A y).det) (0 : E →L[ℝ] ℝ) x := by
  simpa using (zero_jet_det A hA).sqrt hn

lemma zero_jet_density_inverse (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) (i j : ι) :
    HasFDerivAt (fun y => Real.sqrt (A y).det * (A y)⁻¹ i j) (0 : E →L[ℝ] ℝ) x := by
  convert! (zero_jet_density A hA hn).mul (zero_jet_inverse A hA hn i j) using 1
  simp
end YauCounterexamples


end

end OAI
