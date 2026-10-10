import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalFrameOperator
import OAI.Geometry.TamingCompatibility.Elliptic.LocalGarding

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped ContDiff RealInnerProductSpace SchwartzMap

def oneVector : MetricForms.Form V 1 →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma oneVector_apply (a : MetricForms.Form V 1) (i : Fin 4) :
    oneVector a i = a ![e i] := by
  have hv : oneVector a = (InnerProductSpace.toDual ℝ V).symm (oneLinear a) := rfl
  rw [hv]
  have h := InnerProductSpace.toDual_symm_apply (x := e i) (y := oneLinear a)
  simpa only [EuclideanSpace.inner_single_right, e, mul_one, one_mul, conj_trivial, oneLinear_apply] using h

def combine {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) : Pair →L[ℝ] D :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight u + (EuclideanSpace.proj (1 : Fin 2)).smulRight v
lemma combine_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) (q : Pair) :
    combine u v q = q 0 • u + q 1 • v := rfl
lemma combine_pair {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) (a b : ℝ) :
    combine u v (pair a b) = a • u + b • v := rfl

def principal (g : Metric V) (F ψ χ : MetricForms.Form V 2) (i : Fin 4) : Pair →L[ℝ] V :=
  oneVector ∘L starThreeCLM g F ∘L
    combine (wedgeOne (EuclideanSpace.proj i) ψ) (wedgeOne (EuclideanSpace.proj i) χ)

def lower (g : Metric V) (F : MetricForms.Form V 2) (ψ χ : V → MetricForms.Form V 2) (x : V) :
    Pair →L[ℝ] V := oneVector ∘L starThreeCLM g F ∘L combine (extDeriv ψ x) (extDeriv χ x)

def flatPrincipal (i : Fin 4) : Pair →L[ℝ] V :=
  ![combine (e 2) (e 3), combine (-e 3) (e 2),
    combine (-e 0) (-e 1), combine (e 1) (-e 0)] i

lemma flatPrincipal_sum (A B : S) (x : V) :
    (∑ i, flatPrincipal i (pair (coordinateDeriv i A x) (coordinateDeriv i B x))) =
      codifferential A B x := by
  ext j
  fin_cases j <;>
    simp [flatPrincipal,combine_pair,codifferential,e,Fin.sum_univ_succ]
  <;> ring

lemma covector_expansion (ξ : V →L[ℝ] ℝ) : ξ = ∑ i, (ξ (e i)) • EuclideanSpace.proj i := by
  ext x
  have he := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hv : (∑ i, x i • e i) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using he
  calc
    ξ x = ξ (∑ i, x i • e i) := congrArg ξ hv.symm
    _ = ∑ i, x i * ξ (e i) := by simp only [_root_.map_sum,map_smul,smul_eq_mul]
    _ = _ := by simp [mul_comm]

lemma operator_expansion {A B : V → ℝ} {ψ χ : V → MetricForms.Form V 2} {x : V}
    (g : Metric V) (F : MetricForms.Form V 2)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    oneVector (starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      (∑ i, principal g F (ψ x) (χ x) i
        (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i)))) +
      lower g F ψ χ x (pair (A x) (B x)) := by
  rw [LocalFrameOperator.expansion_at g F hA hB hψ hχ]
  simp only [map_add,map_smul]
  apply congrArg₂ (· + ·)
  · have hA' := covector_expansion (fderiv ℝ A x)
    have hB' := covector_expansion (fderiv ℝ B x)
    conv_lhs => rw [hA',hB']
    change oneVector (starThreeCLM g F (wedgeOneRight (ψ x) _)) +
      oneVector (starThreeCLM g F (wedgeOneRight (χ x) _)) = _
    simp only [_root_.map_sum,map_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [principal,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
      starThreeCLM_apply,wedgeOneRight_apply]
  · simp only [lower, ContinuousLinearMap.comp_apply, combine_pair, map_add, map_smul,
      starThreeCLM_apply]

end TamingCompatibility.LocalMatrixOperator

end
end

section

noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

lemma principal_at_unitary_center (g : Metric V)
    (hg : ∀ i j, g.bilinear (e i) (e j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (e 0) = e 1) (h1 : J (e 1) = -e 0)
    (h2 : J (e 2) = e 3) (h3 : J (e 3) = -e 2)
    (F : MetricForms.Form V 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (i : Fin 4) : principal g F (realPart g e) (imagPart g e) i = flatPrincipal i := by
  ext q j
  change oneVector (starThree g F
    (q 0 • wedgeOne (EuclideanSpace.proj i) (realPart g e) +
      q 1 • wedgeOne (EuclideanSpace.proj i) (imagPart g e))) j = _
  rw [starThree_add,starThree_smul,starThree_smul]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,oneVector_apply]
  rw [star_wedge_real g (by simp [V]) e hg J h0 h1 h2 h3 F hF,
      star_wedge_imag g (by simp [V]) e hg J h0 h1 h2 h3 F hF]
  fin_cases i <;> fin_cases j <;> simp [flatPrincipal,combine_apply,e]

lemma principal_smooth {U : Set V} {g : V → Metric V} {F ψ χ : V → MetricForms.Form V 2}
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => principal (g x) (F x) (ψ x) (χ x) i) U := by
  apply contDiffOn_clm_apply.mpr
  intro q
  have hwψ := (wedgeOneBilinear ((ofSubsingletonLIE (0 : Fin 1))
    (EuclideanSpace.proj i))).contDiff.comp_contDiffOn hψ
  have hwχ := (wedgeOneBilinear ((ofSubsingletonLIE (0 : Fin 1))
    (EuclideanSpace.proj i))).contDiff.comp_contDiffOn hχ

  exact oneVector.contDiff.comp_contDiffOn
    (hstar.clm_apply ((hwψ.const_smul (q 0)).add (hwχ.const_smul (q 1))))

lemma lower_smooth {U : Set V} (hU : IsOpen U)
    {g : V → Metric V} {F ψ χ : V → MetricForms.Form V 2}
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) :
    ContDiffOn ℝ ∞ (fun x => lower (g x) (F x) ψ χ x) U := by
  apply contDiffOn_clm_apply.mpr
  intro q
  have hdψ : ContDiffOn ℝ ∞ (fun x => extDeriv ψ x) U :=
    (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn (hψ.fderiv_of_isOpen hU (by simp))
  have hdχ : ContDiffOn ℝ ∞ (fun x => extDeriv χ x) U :=
    (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn (hχ.fderiv_of_isOpen hU (by simp))
  exact oneVector.contDiff.comp_contDiffOn
    (hstar.clm_apply ((hdψ.const_smul (q 0)).add (hdχ.const_smul (q 1))))

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
