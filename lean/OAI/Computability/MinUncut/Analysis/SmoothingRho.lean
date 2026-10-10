import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussNegPreserving
import OAI.Computability.MinUncut.Estimates.Convolution

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma project_const_mul (d : ℕ) (a : ℝ) (f : (ι → ℝ) → ℝ) :
    project d (fun x => a*f x) = fun x => a*project d f x := by
  funext x
  simp only [project, coeff_const_mul, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
lemma convolutionGradient_memLp {σ : ℝ} (hσ : σ ≠ 0) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (i : ι) :
    MemLp (convolutionGradient σ Q i) 2 (γpi ι) := by
  rw [convolutionGradient_as_noise (ρ := 1) one_ne_zero hσ]
  exact memLp_gradient 1 (σ*1) (hQ.comp (by fun_prop)) (fun x => hb _) i

def smoothingRho (σ : ℝ) : ℝ := (Real.sqrt (1+σ^2))⁻¹
lemma smoothingRho_pos (σ : ℝ) : 0 < smoothingRho σ := by
  unfold smoothingRho
  positivity
lemma smoothingRho_rotation (σ : ℝ) :
    (smoothingRho σ)^2+(σ*smoothingRho σ)^2=1 := by
  have hs : (Real.sqrt (1+σ^2))^2 = 1+σ^2 := Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (1+σ^2) ≠ 0 := ne_of_gt (by positivity)
  unfold smoothingRho
  field_simp
  nlinarith
lemma smoothingRho_lt_one {σ : ℝ} (hσ : σ ≠ 0) : |smoothingRho σ| < 1 := by
  rw [abs_of_pos (smoothingRho_pos σ)]
  unfold smoothingRho
  apply (inv_lt_one₀ (by positivity : 0 < Real.sqrt (1+σ^2))).2
  have he := Real.sq_sqrt (by positivity : 0 ≤ 1+σ^2)
  nlinarith [Real.sqrt_nonneg (1+σ^2), sq_pos_of_ne_zero hσ]
end MinUncut.GaussianHermite

namespace MinUncut.Inner
open GaussianHermite
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [Fintype A] {m n : ℕ}

lemma gradient_as_convolutionGradient (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) *
      convolutionGradient σ (tableSmooth f B η) x c := by
  rw [gradient_score f B hσ]
  unfold GaussianHermite.convolutionGradient
  simp only [div_eq_mul_inv, mul_assoc]
  rfl

lemma gradient_memLp (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) :
    MemLp (fun c => gradient f B σ η c x) 2 (gauss (Point m n)) := by
  simp_rw [gradient_as_convolutionGradient f B hσ]
  exact (convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
    (tableSmooth_abs_le f B η) x).const_mul _

lemma spatialEnergy_sqrt_scale (hn : 0 < n) (v : Point m n → ℝ) :
    spatialEnergy (fun x => Real.sqrt (n^m : ℕ)*v x) = ∑ x, (v x)^2 := by
  have hN : (0 : ℝ) < (n^m : ℕ) := by exact_mod_cast pow_pos hn m
  simp only [spatialEnergy, mul_pow, Real.sq_sqrt hN.le, ← Finset.mul_sum]
  exact inv_mul_cancel_left₀ (ne_of_gt hN) _

lemma gradient_integral_energy (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) :
    (∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n)) =
      ∑ x, ∫ c, (convolutionGradient σ (tableSmooth f B η) x c)^2
        ∂gauss (Point m n) := by
  simp_rw [show ∀ c, gradient f B σ η c = fun x => Real.sqrt (n^m : ℕ)*
    convolutionGradient σ (tableSmooth f B η) x c by
      intro c; funext x; exact gradient_as_convolutionGradient f B hσ η c x,
    spatialEnergy_sqrt_scale hn]
  exact integral_finsetSum _ (fun x _ =>
    (convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η) x).integrable_sq)

lemma smooth_energy_le_gradient (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) :
    (∫ c, (smooth f B σ η c)^2 ∂gauss (Point m n)) ≤
      ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  rw [gradient_integral_energy f B hn hσ]
  exact convolution_poincare (ne_of_gt (smoothingRho_pos σ)) hσ
    (smoothingRho_rotation σ) (measurable_tableSmooth f B η)
    (tableSmooth_abs_le f B η) (smooth_mean_zero f B σ hη)

def gaussianProject (d : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  GaussianHermite.project d (fun c => gradient f B σ η c x) c

lemma gaussian_residual_energy (d : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) :
    (∫ c, spatialEnergy (fun x => gradient f B σ η c x -
      gaussianProject d f B σ η c x) ∂gauss (Point m n)) =
    ∑ x, ∫ c, (convolutionGradient σ (tableSmooth f B η) x c -
       GaussianHermite.project d (convolutionGradient σ (tableSmooth f B η) x) c)^2
         ∂gauss (Point m n) := by
  simp only [gaussianProject]
  simp_rw [gradient_as_convolutionGradient f B hσ, project_const_mul, ← mul_sub,
    spatialEnergy_sqrt_scale hn]
  exact integral_finsetSum _ (fun x _ =>
    ((convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η) x).sub (memLp_project d _)).integrable_sq)

theorem exists_gaussian_cutoff {σ ε : ℝ} (hσ : σ ≠ 0) (hε : 0 < ε) :
    ∃ d : ℕ, ∀ (m n : ℕ) (_hn : 0 < n) (f : FoldedProof A)
      (B : FaceArray A m n) (η : ℝ),
      (∫ c, spatialEnergy (fun x => gradient f B σ η c x -
        gaussianProject d f B σ η c x) ∂gauss (Point m n)) ≤ ε := by
  obtain ⟨d, hd⟩ := exists_cutoff (smoothingRho_lt_one hσ) hε
  refine ⟨d, fun m n hn f B η => ?_⟩
  rw [gaussian_residual_energy d f B hn hσ]
  exact convolution_gradient_tail (ne_of_gt (smoothingRho_pos σ)) hσ
    (smoothingRho_rotation σ) hε.le d hd (measurable_tableSmooth f B η)
    (tableSmooth_abs_le f B η)
end MinUncut.Inner

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace

end

end OAI
