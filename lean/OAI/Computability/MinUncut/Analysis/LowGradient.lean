import Mathlib
import OAI.Computability.MinUncut.Estimates.SecondFailureIndicator

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def lowGradient (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  selectedProject (rectangle D s) (fun B c => gradient f B σ η c x) B c

lemma lowGradient_composition (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) :
    lowGradient D s f σ η B c x = RowNoise.project D
      (fun C => GaussianHermite.project s (fun d => gradient f C σ η d x) c) B :=
  rectangle_eq_composition _ _ _ _ _

lemma lowGradient_memLp (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (x : Point m n) :
    MemLp (fun c => lowGradient D s f σ η B c x) 2 (gauss (Point m n)) :=
  memLp_selectedProject _ _ _

def averagedEnergy (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ) : ℝ :=
  𝔼 B, ∫ c, spatialEnergy (u B c) ∂gauss (Point m n)

lemma averagedEnergy_eq_jointEnergy
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (hu : ∀ B x, MemLp (fun c => u B c x) 2 (gauss (Point m n))) :
    averagedEnergy u = ((n^m:ℕ):ℝ)⁻¹*∑ x, jointEnergy (fun B c => u B c x) := by
  simp only [averagedEnergy,spatialEnergy,integral_const_mul,
    integral_finsetSum _ (fun x _ => (hu _ x).integrable_sq),
    ← Finset.mul_expect,Finset.expect_sum_comm,jointEnergy]
  rfl

lemma lowGradient_energy_identity (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (lowGradient D s f σ η) =
      averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c)-
      averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) := by
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η),
    averagedEnergy_eq_jointEnergy _ (fun B x => gradient_memLp f B hσ η x),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (lowGradient_memLp D s f σ η B x))]
  simp only [lowGradient,rectangle_energy_identity _ _ _ (fun B => gradient_memLp f B hσ η _),
    Finset.sum_sub_distrib,mul_sub]

lemma lowGradient_residual_le (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) ≤
      2*averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-rowProjectedGradient D f σ η B c x)+
      2*averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) := by
  have hg (B : FaceArray A m n) (x : Point m n) :
      MemLp (fun c => gaussianProject s f B σ η c x) 2 (gauss (Point m n)) :=
    GaussianHermite.memLp_project _ _
  rw [averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (lowGradient_memLp D s f σ η B x)),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-rowProjectedGradient D f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (rowProjectedGradient_memLp D f B hσ η x)),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) (fun B x => (gradient_memLp f B hσ η x).sub (hg B x))]
  calc
    _ ≤ ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        (2*jointEnergy (fun B c => gradient f B σ η c x-rowProjectedGradient D f σ η B c x)+
         2*jointEnergy (fun B c => gradient f B σ η c x-gaussianProject s f B σ η c x)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ =>
        rectangle_residual_le D s _ (fun B => gradient_memLp f B hσ η x))) (by positivity)
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]; ring

lemma averagedEnergy_gradient_le (f : FoldedProof A) (hn : 0 < n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c) ≤ σ⁻¹^2 := by
  have he (B : FaceArray A m n) :
      (∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n)) ≤ σ⁻¹^2 := by
    have hi : Integrable (fun c => spatialEnergy (gradient f B σ η c)) (gauss (Point m n)) :=
      (integrable_finsetSum _ (fun x _ => (gradient_memLp f B hσ η x).integrable_sq)).const_mul _
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const (σ⁻¹^2)) (gradient_spatialEnergy_le f B hn hσ η)
  simpa [averagedEnergy] using Finset.expect_le_expect (s := Finset.univ) (fun B _ => he B)

lemma averagedEnergy_lowGradient_le (D s : ℕ) (f : FoldedProof A) (hn : 0 < n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (lowGradient D s f σ η) ≤ σ⁻¹^2 := by
  apply le_trans _ (averagedEnergy_gradient_le (m := m) f hn hσ η)
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η),
    averagedEnergy_eq_jointEnergy _ (fun B x => gradient_memLp f B hσ η x)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ =>
    selectedProject_energy_le _ _ (fun B => gradient_memLp f B hσ η x))) (by positivity)
end MinUncut.Inner

end

end OAI
