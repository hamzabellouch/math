import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalMatrixOperator

namespace OAI

section
section
section

section

noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace
namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy

def directionDeriv (b : Fin 4 → V) (i : Fin 4) (f : S) : S := ∂_{b i} f
lemma second_partial_comm (b : Fin 4 → V) (i j : Fin 4) (f : S) :
    directionDeriv b i (directionDeriv b j f) = directionDeriv b j (directionDeriv b i f) := by
  ext x
  simp only [directionDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((f.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change (fderiv ℝ (fun y => fderiv ℝ f y (b j)) x) (b i) =
    (fderiv ℝ (fun y => fderiv ℝ f y (b i)) x) (b j)
  rw [fderiv_clm_apply hf (differentiableAt_const _),
    fderiv_clm_apply hf (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact ((f.smooth 2).contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) _ _

lemma partial_mul_integral_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    (∫ x, directionDeriv b i f x * directionDeriv b j g x) = ∫ x, directionDeriv b j f x * directionDeriv b i g x := by
  have hi := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (directionDeriv b j g) (b i)
  have hj := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (directionDeriv b i g) (b j)
  change (∫ x, f x * directionDeriv b i (directionDeriv b j g) x) = -(∫ x, directionDeriv b i f x * directionDeriv b j g x) at hi
  change (∫ x, f x * directionDeriv b j (directionDeriv b i g) x) = -(∫ x, directionDeriv b j f x * directionDeriv b i g x) at hj
  rw [second_partial_comm] at hi
  linarith

def codifferential (b : Fin 4 → V) (A B : S) (x : V) : V := WithLp.toLp 2
  ![-directionDeriv b 2 A x - directionDeriv b 3 B x, -directionDeriv b 2 B x + directionDeriv b 3 A x,
    directionDeriv b 0 A x + directionDeriv b 1 B x, directionDeriv b 0 B x - directionDeriv b 1 A x]

def gradientEnergy (b : Fin 4 → V) (A B : S) (x : V) : ℝ :=
  ∑ i : Fin 4, ((directionDeriv b i A x)^2 + (directionDeriv b i B x)^2)

lemma gradientEnergy_integrable (b : Fin 4 → V) (A B : S) : Integrable (gradientEnergy b A B) := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    (schwartz_sq_integrable (directionDeriv b i A)).add (schwartz_sq_integrable (directionDeriv b i B))

lemma codifferential_energy_pointwise (b : Fin 4 → V) (A B : S) (x : V) :
    ‖codifferential b A B x‖^2 = gradientEnergy b A B x +
      2 * (directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
        directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) := by
  simp [codifferential, EuclideanSpace.real_norm_sq_eq, gradientEnergy, Fin.sum_univ_succ]
  ring

theorem codifferential_energy (b : Fin 4 → V) (A B : S) :
    (∫ x, ‖codifferential b A B x‖^2) = ∫ x, gradientEnergy b A B x := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (directionDeriv b i A) (directionDeriv b j B)
  simp_rw [codifferential_energy_pointwise]
  have hC : Integrable (fun x =>
      directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
      directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) :=
    (((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)
  calc
    _ = (∫ x, gradientEnergy b A B x) +
        ∫ x, 2 * (directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
          directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) :=
      integral_add (gradientEnergy_integrable b A B) (hC.const_mul 2)
    _ = _ := by
      have hsub := integral_sub (((hm 2 3).sub (hm 3 2)).add (hm 0 1)) (hm 1 0)
      have hadd := integral_add ((hm 2 3).sub (hm 3 2)) (hm 0 1)
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd
      rw [integral_const_mul, hsub, hadd, integral_sub (hm 2 3) (hm 3 2),
        partial_mul_integral_swap b 2 3 A B, partial_mul_integral_swap b 0 1 A B]
      ring

end TamingCompatibility.DirectionalEnergy

end
end

section

noncomputable section
namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy LocalMatrixOperator
open MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

def coordinateConstant (b : Module.Basis (Fin 4) ℝ V) : ℝ :=
  1 + ∑ i : Fin 4, ∑ j : Fin 4, (b.repr (e i) j)^2
lemma coordinateConstant_pos (b : Module.Basis (Fin 4) ℝ V) : 0 < coordinateConstant b := by
  unfold coordinateConstant
  positivity

lemma covector_basis_expansion (b : Module.Basis (Fin 4) ℝ V) (ξ : V →L[ℝ] ℝ) (u : V) :
    ξ u = ∑ j, b.repr u j * ξ (b j) := by
  calc
    ξ u = ξ (∑ j, b.repr u j • b j) := congrArg ξ (b.sum_repr u).symm
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]

lemma covector_basis_sq (b : Module.Basis (Fin 4) ℝ V) (ξ : V →L[ℝ] ℝ) (i : Fin 4) :
    (ξ (e i))^2 ≤ (∑ j, (b.repr (e i) j)^2) * ∑ j, (ξ (b j))^2 := by
  rw [covector_basis_expansion b ξ (e i)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma gradient_control (b : Module.Basis (Fin 4) ℝ V) (A B : S) (x : V) :
    EuclideanEnergy.gradientEnergy A B x ≤ coordinateConstant b * gradientEnergy b A B x := by
  have hA (i : Fin 4) := covector_basis_sq b (fderiv ℝ A x) i
  have hB (i : Fin 4) := covector_basis_sq b (fderiv ℝ B x) i
  have hdir (i : Fin 4) : (coordinateDeriv i A x)^2 + (coordinateDeriv i B x)^2 ≤
      (∑ j, (b.repr (e i) j)^2) * gradientEnergy b A B x := by
    simpa only [coordinateDeriv,directionDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      gradientEnergy,Finset.sum_add_distrib,mul_add] using add_le_add (hA i) (hB i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdir i)
  change EuclideanEnergy.gradientEnergy A B x ≤ _ at h
  rw [← Finset.sum_mul] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (by simp [coordinateConstant])
    (Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

end TamingCompatibility.DirectionalEnergy

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricForms ExteriorForms MetricHodge AntiInvariantFrame
open scoped RealInnerProductSpace SchwartzMap LineDeriv

lemma oneVector_inner (a : MetricForms.Form V 1) (u : V) :
    inner ℝ (oneVector a) u = a ![u] := by
  have hv : oneVector a = (InnerProductSpace.toDual ℝ V).symm (oneLinear a) := rfl
  rw [hv,InnerProductSpace.toDual_symm_apply,oneLinear_apply]

def oneCoordinates (b : Fin 4 → V) (a : MetricForms.Form V 1) : V :=
  WithLp.toLp 2 (fun i => a ![b i])

def evaluationConstant (b : Fin 4 → V) : ℝ := 1 + ∑ i, ‖b i‖^2
lemma evaluationConstant_pos (b : Fin 4 → V) : 0 < evaluationConstant b := by
  unfold evaluationConstant
  positivity
lemma oneCoordinates_bound (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    ‖oneCoordinates b a‖^2 ≤ evaluationConstant b * ‖oneVector a‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have h (i : Fin 4) : (a ![b i])^2 ≤ ‖b i‖^2 * ‖oneVector a‖^2 := by
    rw [← oneVector_inner]
    have h := sq_le_sq₀ (abs_nonneg _) (by positivity)
      |>.mpr (abs_real_inner_le_norm (oneVector a) (b i))
    simpa only [sq_abs,mul_pow,mul_comm] using h
  change (∑ i, (a ![b i])^2) ≤ _
  refine (Finset.sum_le_sum (fun i _ => h i)).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by simp [evaluationConstant]) (sq_nonneg _)

lemma principal_covectors (g : MetricModel.Metric V) (F ψ χ : MetricForms.Form V 2)
    (ξ η : V →L[ℝ] ℝ) :
    oneVector (starThree g F (wedgeOne ξ ψ + wedgeOne η χ)) =
      ∑ i, principal g F ψ χ i (pair (ξ (e i)) (η (e i))) := by
  rw [starThree_add,map_add]
  conv_lhs => rw [covector_expansion ξ,covector_expansion η]
  change oneVector (starThreeCLM g F (wedgeOneRight ψ _)) +
    oneVector (starThreeCLM g F (wedgeOneRight χ _)) = _
  simp only [map_sum,map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [principal,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
    starThreeCLM_apply,wedgeOneRight_apply]

lemma oneCoordinates_star_covectors (g : MetricModel.Metric V)
    (b : Fin 4 → V) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (F : MetricForms.Form V 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (A B : S) (x : V) :
    oneCoordinates b (starThree g F (wedgeOne (fderiv ℝ A x) (realPart g b) +
      wedgeOne (fderiv ℝ B x) (imagPart g b))) = DirectionalEnergy.codifferential b A B x := by
  ext i
  change starThree g F _ ![b i] = _
  rw [starThree_add,ContinuousAlternatingMap.add_apply,
    star_wedge_real g (by simp [V]) b hb J h0 h1 h2 h3 F hF,
    star_wedge_imag g (by simp [V]) b hb J h0 h1 h2 h3 F hF]
  fin_cases i <;> simp [DirectionalEnergy.codifferential,DirectionalEnergy.directionDeriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] <;> ring

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
