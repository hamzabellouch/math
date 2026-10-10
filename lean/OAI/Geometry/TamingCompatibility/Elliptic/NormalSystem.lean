import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalSymbol

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

def frameVector (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ContinuousAlternatingMap.apply ℝ V ℝ ![b i])
lemma frameVector_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) (i : Fin 4) :
    frameVector b a i = a ![b i] := rfl

def frameCovector (b : Fin 4 → V) (i : Fin 4) : V := WithLp.toLp 2 (fun j => b j i)

def normalPrincipal (b : Fin 4 → V) (i : Fin 4) : Pair →L[ℝ] V :=
  normalSymbol (frameCovector b i)

def normalLower (g : Metric V) (F : MetricForms.Form V 2) (ψ χ : V → MetricForms.Form V 2)
    (b : Fin 4 → V) (x : V) : Pair →L[ℝ] V :=
  frameVector b ∘L starThreeCLM g F ∘L combine (extDeriv ψ x) (extDeriv χ x)

lemma frameVector_pairing (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c : MetricForms.Form V 1) :
    ⟪frameVector b a,frameVector b c⟫ = pairing g a c := by
  rw [pairing_one_eq_sum g (by simp [V]) b hb]
  simp only [PiLp.inner_apply,frameVector_apply,RCLike.inner_apply,conj_trivial,mul_comm]

lemma normal_operator_expansion {A B : V → ℝ} {ψ χ : V → MetricForms.Form V 2} {x : V}
    (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (hψx : ψ x = realPart g b) (hχx : χ x = imagPart g b)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    frameVector b (starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      (∑ i, normalPrincipal b i (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i)))) +
      normalLower g F ψ χ b x (pair (A x) (B x)) := by
  rw [LocalFrameOperator.expansion_at g F hA hB hψ hχ]
  simp only [map_add,map_smul]
  apply congrArg₂ (· + ·)
  · have hA' := covector_expansion (fderiv ℝ A x)
    have hB' := covector_expansion (fderiv ℝ B x)
    conv_lhs => rw [hA',hB']
    change frameVector b (starThreeCLM g F (wedgeOneRight (ψ x) _)) +
      frameVector b (starThreeCLM g F (wedgeOneRight (χ x) _)) = _
    simp only [_root_.map_sum,map_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ext j
    have hn := normalSymbol_geometric g (by simp [V]) b hb J h0 h1 h2 h3 F hF
      (EuclideanSpace.proj i) (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i))) j
    rw [← hψx,← hχx] at hn
    change (starThree g F (wedgeOne (EuclideanSpace.proj i)
      ((fderiv ℝ A x (e i)) • ψ x + (fderiv ℝ B x (e i)) • χ x))) ![b j] = _ at hn
    have hw : wedgeOne (EuclideanSpace.proj i)
        ((fderiv ℝ A x (e i)) • ψ x + (fderiv ℝ B x (e i)) • χ x) =
      (fderiv ℝ A x (e i)) • wedgeOne (EuclideanSpace.proj i) (ψ x) +
      (fderiv ℝ B x (e i)) • wedgeOne (EuclideanSpace.proj i) (χ x) := by
      change (wedgeOneBilinear (E := V) (ofSubsingletonLIE (0 : Fin 1) (EuclideanSpace.proj i))) _ = _
      rw [map_add,map_smul,map_smul]
      rfl
    rw [hw,starThree_add,starThree_smul,starThree_smul] at hn
    simpa only [frameVector_apply,normalPrincipal,frameCovector,starThreeCLM_apply,
      wedgeOneRight_apply,starThree_add,starThree_smul,ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
      pair,PiLp.proj_apply] using hn
  · simp only [normalLower,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
      starThreeCLM_apply]

end TamingCompatibility.LocalMatrixOperator

end

end OAI
