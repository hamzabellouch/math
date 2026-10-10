import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.ComplexHessian
import OAI.Geometry.PrescribedPotential.CutoffHigher

namespace OAI

/-! Hessian Commutator. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def secondLocalizedError (κ : 𝓢(E, ℂ)) (v a b : E) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (∂_{a} κ : 𝓢(E, ℂ)) ∘L
    (lineDerivOpCLM ℂ 𝓢(E, ℂ) b ∘L lineDerivOpCLM ℂ 𝓢(E, ℂ) v) +
  SchwartzMap.smulLeftCLM ℂ (∂_{b} κ : 𝓢(E, ℂ)) ∘L
    (lineDerivOpCLM ℂ 𝓢(E, ℂ) a ∘L lineDerivOpCLM ℂ 𝓢(E, ℂ) v) +
  SchwartzMap.smulLeftCLM ℂ (∂_{a} (∂_{b} κ) : 𝓢(E, ℂ)) ∘L
    lineDerivOpCLM ℂ 𝓢(E, ℂ) v

lemma secondLocalizedError_identity (κ f : 𝓢(E, ℂ)) (v a b : E) :
    ∂_{a} (∂_{b} (SchwartzMap.smulLeftCLM ℂ κ (∂_{v} f))) =
      SchwartzMap.smulLeftCLM ℂ κ (∂_{v} (∂_{a} (∂_{b} f))) +
        secondLocalizedError κ v a b f := by
  rw [schwartz_second_product]
  have hd : ∂_{a} (∂_{b} (∂_{v} f)) = ∂_{v} (∂_{a} (∂_{b} f)) := by
    rw [schwartz_deriv_comm b v, schwartz_deriv_comm a v]
  rw [hd]
  rfl

lemma secondLocalizedError_bound (κ : 𝓢(E, ℂ)) (v a b : E) (k : ℕ) :
    CoreBound ((k : ℝ)+2) (k : ℝ) (secondLocalizedError κ v a b) := by
  have hd (w : E) : CoreBound ((k : ℝ)+2) (k : ℝ)
      (fun f : 𝓢(E, ℂ) => ∂_{w} (∂_{v} f)) :=
    (coreBound_deriv w (s := (k : ℝ)+1) (t := (k : ℝ)) (by linarith)).comp
      (coreBound_deriv v (s := (k : ℝ)+2) (t := (k : ℝ)+1) (by linarith))
  exact ((coreBound_product_integer (∂_{a} κ) k).comp (hd b)).add
    ((coreBound_product_integer (∂_{b} κ) k).comp (hd a)) |>.add
      ((coreBound_product_integer (∂_{a} (∂_{b} κ)) k).comp
        (coreBound_deriv v (s := (k : ℝ)+2) (t := (k : ℝ)) (by linarith)))
end SobolevChart

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ}

def hessianLocalizedError (κ : 𝓢(EC d, ℂ)) (v : EC d) (i j : Fin d) :
    𝓢(EC d, ℂ) →L[ℂ] 𝓢(EC d, ℂ) :=
  (1/4 : ℂ) • (secondLocalizedError κ v (hessianDirection i) (hessianDirection j) +
    secondLocalizedError κ v (hessianIDirection i) (hessianIDirection j) +
      Complex.I • (secondLocalizedError κ v (hessianIDirection i) (hessianDirection j) +
        (-1 : ℂ) • secondLocalizedError κ v (hessianDirection i) (hessianIDirection j)))

lemma hessianLocalizedError_identity (κ f : 𝓢(EC d, ℂ)) (v : EC d) (i j : Fin d) :
    hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ κ (∂_{v} f)) =
      SchwartzMap.smulLeftCLM ℂ κ (∂_{v} (hessianEntrySchwartz i j f)) +
        hessianLocalizedError κ v i j f := by
  simp only [hessianEntrySchwartz, hessianLocalizedError, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    secondLocalizedError_identity, lineDerivOp_add, lineDerivOp_smul, map_smul, map_add]
  module

lemma hessianLocalizedError_bound (κ : 𝓢(EC d, ℂ)) (v : EC d) (i j : Fin d) (k : ℕ) :
    CoreBound ((k : ℝ)+2) (k : ℝ) (hessianLocalizedError κ v i j) := by
  exact ((secondLocalizedError_bound κ v _ _ k).add
    (secondLocalizedError_bound κ v _ _ k) |>.add
      (((secondLocalizedError_bound κ v _ _ k).add
        ((secondLocalizedError_bound κ v _ _ k).smul (-1))).smul Complex.I)).smul (1/4)
end GlobalElliptic

end
end

end OAI
