import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.DirectionalEnergy

namespace OAI

section
section
section

section

noncomputable section
open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

def system (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) (x : V) : V :=
  (∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))) +
    b x (pair (A x) (B x))
lemma system_integrable (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) {δ C : ℝ} (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => ‖system a b A B x‖^2) := by
  have hcont : Continuous (system a b A B) := by
    apply Continuous.add _ (hbc.clm_apply (pair_continuous A.continuous B.continuous))
    apply continuous_finsetSum
    intro i _
    exact (hac i).clm_apply (pair_continuous (coordinateDeriv i A).continuous
      (coordinateDeriv i B).continuous)
  have hdom := ((gradientEnergy_integrable A B).const_mul (8*δ^2)).add
    (((schwartz_sq_integrable A).add (schwartz_sq_integrable B)).const_mul (2*C^2))
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := norm_add_sq_le
    (∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x)))
    (b x (pair (A x) (B x)))
  have hp := principalError_bound a A B x (ha x)
  have hl := lowerError_bound b A B x (hb x)
  dsimp only [system,Pi.add_apply]
  nlinarith

def constantSystem (c : Fin 4 → Pair →L[ℝ] V) (A B : S) (x : V) : V :=
  ∑ i, c i (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
lemma constantSystem_integrable (c : Fin 4 → Pair →L[ℝ] V) (A B : S) :
    Integrable (fun x => ‖constantSystem c A B x‖^2) := by
  have h := system_integrable (fun i _ => c i) (fun _ => 0) A B
    (δ := ∑ i, ‖c i‖) (C := 0) (fun _ => continuous_const) continuous_const
    (fun _ i => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (fun _ => by simp)
  simpa only [system,zero_apply,add_zero,constantSystem] using h

end TamingCompatibility.MatrixEnergy

namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy
lemma codifferential_integrable_sq (b : Fin 4 → V) (A B : S) :
    Integrable (fun x => ‖codifferential b A B x‖^2) := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (directionDeriv b i A) (directionDeriv b j B)
  simp_rw [codifferential_energy_pointwise]
  exact (gradientEnergy_integrable b A B).add
    (((((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)).const_mul 2)
end TamingCompatibility.DirectionalEnergy

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricForms ExteriorForms MetricHodge AntiInvariantFrame
open MatrixEnergy

lemma frozen_geometric_energy (g : MetricModel.Metric V)
    (b : Module.Basis (Fin 4) ℝ V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (F : MetricForms.Form V 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (A B : S) :
    (∫ x, gradientEnergy A B x) ≤
      (DirectionalEnergy.coordinateConstant b * evaluationConstant b) *
      ∫ x, ‖constantSystem (principal g F (realPart g b) (imagPart g b)) A B x‖^2 := by
  let c := principal g F (realPart g b) (imagPart g b)
  have he (x : V) : oneVector (starThree g F
      (wedgeOne (fderiv ℝ A x) (realPart g b) +
        wedgeOne (fderiv ℝ B x) (imagPart g b))) = constantSystem c A B x := by
    simpa only [constantSystem,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
      using principal_covectors g F (realPart g b) (imagPart g b) (fderiv ℝ A x) (fderiv ℝ B x)
  have hp (x : V) : ‖DirectionalEnergy.codifferential b A B x‖^2 ≤
      evaluationConstant b * ‖constantSystem c A B x‖^2 := by
    rw [← oneCoordinates_star_covectors g b hb J h0 h1 h2 h3 F hF A B x]
    simpa only [he] using oneCoordinates_bound b (starThree g F
      (wedgeOne (fderiv ℝ A x) (realPart g b) + wedgeOne (fderiv ℝ B x) (imagPart g b)))
  have hI := integral_mono (DirectionalEnergy.codifferential_integrable_sq b A B)
    ((constantSystem_integrable c A B).const_mul (evaluationConstant b)) hp
  rw [integral_const_mul,DirectionalEnergy.codifferential_energy] at hI
  have hG := integral_mono (gradientEnergy_integrable A B)
    ((DirectionalEnergy.gradientEnergy_integrable b A B).const_mul
      (DirectionalEnergy.coordinateConstant b)) (DirectionalEnergy.gradient_control b A B)
  rw [integral_const_mul] at hG
  calc
    _ ≤ DirectionalEnergy.coordinateConstant b * (∫ x, DirectionalEnergy.gradientEnergy b A B x) := hG
    _ ≤ DirectionalEnergy.coordinateConstant b *
        (evaluationConstant b * (∫ x, ‖constantSystem c A B x‖^2)) :=
      mul_le_mul_of_nonneg_left hI (DirectionalEnergy.coordinateConstant_pos b).le
    _ = _ := by rw [mul_assoc]

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
