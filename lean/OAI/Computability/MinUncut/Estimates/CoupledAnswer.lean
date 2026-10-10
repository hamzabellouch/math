import Mathlib
import OAI.Computability.MinUncut.Estimates.F2
import OAI.Computability.MinUncut.Analysis.Gradient

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
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def coupledAnswer (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  bitSign (f.answer (pullQuery B (c+σ•p.1) (η•p.2)))

def secondFailure (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  if f.answer (pullQuery B (c+σ•p.1) (η•p.2)) =
    f.answer (pullQuery C (c+σ•p.1) (η•p.2)) then 0 else 1

def secondRejection (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ p, secondFailure f B C σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n))

lemma coupledAnswer_measurable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : Measurable (coupledAnswer f B σ η c) := by
  have hg : Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ•p.1,p.2)) := by fun_prop
  exact (measurable_answer f B η).comp hg

lemma coupledAnswer_memLp (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    MemLp (coupledAnswer f B σ η c) 2 ((gauss (Point m n)).prod (gauss (Code m n))) :=
  MemLp.of_bound (coupledAnswer_measurable f B σ η c).aestronglyMeasurable 1
    (ae_of_all _ (fun p => by simp only [Real.norm_eq_abs,coupledAnswer,bitSign_abs,le_refl]))

omit [Fintype A] in
lemma secondFailure_eq (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    (coupledAnswer f B σ η c p-coupledAnswer f C σ η c p)^2 = 4*secondFailure f B C σ η c p := by
  unfold coupledAnswer secondFailure
  cases f.answer (pullQuery B (c+σ•p.1) (η•p.2)) <;>
    cases f.answer (pullQuery C (c+σ•p.1) (η•p.2)) <;> norm_num [bitSign]

lemma coupled_score_integrable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) :
    Integrable (fun p => p.1 x*coupledAnswer f B σ η c p)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
  ((GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))).integrable_mul
    (coupledAnswer_memLp f B σ η c)

lemma gradient_coupled_score (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x=Real.sqrt (n^m:ℕ)/σ*
      ∫ p, p.1 x*coupledAnswer f B σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n)) := by
  rw [integral_prod _ (coupled_score_integrable f B σ η c x)]
  exact gradient_convolution f B hσ η c x

theorem gradient_second_comparison (f : FoldedProof A) (B C : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (fun x => gradient f B σ η c x-gradient f C σ η c x) ≤
      4*σ⁻¹^2*secondRejection f B C σ η c := by
  let μ := (gauss (Point m n)).prod (gauss (Code m n))
  let D := fun p => coupledAnswer f B σ η c p-coupledAnswer f C σ η c p
  have hD : MemLp D 2 μ := (coupledAnswer_memLp f B σ η c).sub (coupledAnswer_memLp f C σ η c)
  have hX (x : Point m n) : MemLp (fun p => p.1 x) 2 μ :=
    (GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))
  have hXX (x y : Point m n) : (∫ p, p.1 x*p.1 y ∂μ)=if x=y then 1 else 0 := by
    have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => p.1 x*p.1 y) μ :=
      (hX x).integrable_mul (hX y)
    change (∫ p, p.1 x*p.1 y ∂(gauss (Point m n)).prod (gauss (Code m n)))=_
    rw [integral_prod _ hi]
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul,gauss,GaussianSmoothing.gamma] using GaussianSmoothing.coordinate_second_moment x y
  have hS := GaussianSmoothing.integral_bessel hX hXX hD
  have hN : (0 : ℝ)<(n^m:ℕ) := by exact_mod_cast pow_pos hn m
  have hd (x : Point m n) :
      gradient f B σ η c x-gradient f C σ η c x =
      Real.sqrt (n^m:ℕ)/σ*(∫ p, p.1 x*D p ∂μ) := by
    rw [gradient_coupled_score f B hσ,gradient_coupled_score f C hσ]
    simp only [D,mul_sub]
    rw [integral_sub (coupled_score_integrable f B σ η c x) (coupled_score_integrable f C σ η c x)]
    ring
  have he : spatialEnergy (fun x => gradient f B σ η c x-gradient f C σ η c x) =
      σ⁻¹^2*∑ x, (∫ p, p.1 x*D p ∂μ)^2 := by
    simp only [spatialEnergy,hd,mul_pow,div_pow,Real.sq_sqrt hN.le,← Finset.mul_sum]
    field_simp
  rw [he]
  calc
    _ ≤ σ⁻¹^2*(∫ p, (D p)^2 ∂μ) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by
      simp_rw [D,secondFailure_eq]
      rw [integral_const_mul]
      change σ⁻¹^2*(4*secondRejection f B C σ η c)=_
      ring
end MinUncut.Inner

end

end OAI
