import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexHessian
import OAI.Geometry.PrescribedPotential.CutoffHigher
import OAI.Geometry.PrescribedRicci.UniformSchwartz

namespace OAI

/-! Schwartz Hessian Words. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzWord_deriv (ws : List E) (v : E) (f : 𝓢(E,ℂ)) :
    schwartzWord ws (∂_{v} f) = ∂_{v} (schwartzWord ws f) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change ∂_{a} (schwartzWord ws (∂_{v} f)) = ∂_{v} (∂_{a} (schwartzWord ws f))
    rw [ih,schwartz_deriv_comm]

def wordSecondError (κ : 𝓢(E,ℂ)) (ws : List E) (a b : E) :
    𝓢(E,ℂ) → 𝓢(E,ℂ) := fun f =>
  SchwartzMap.smulLeftCLM ℂ (∂_{a} κ : 𝓢(E,ℂ)) (∂_{b} (schwartzWord ws f)) +
  SchwartzMap.smulLeftCLM ℂ (∂_{b} κ : 𝓢(E,ℂ)) (∂_{a} (schwartzWord ws f)) +
  SchwartzMap.smulLeftCLM ℂ (∂_{a} (∂_{b} κ) : 𝓢(E,ℂ)) (schwartzWord ws f)

lemma wordSecondError_identity (κ f : 𝓢(E,ℂ)) (ws : List E) (a b : E) :
    ∂_{a} (∂_{b} (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws f))) =
      SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws (∂_{a} (∂_{b} f))) +
        wordSecondError κ ws a b f := by
  rw [schwartz_second_product,schwartzWord_deriv,schwartzWord_deriv]
  rfl

lemma wordSecondError_bound (κ : 𝓢(E,ℂ)) (ws : List E) (a b : E) :
    CoreBound ((ws.length:ℝ)+1) 0 (wordSecondError κ ws a b) := by
  have hw : CoreBound ((ws.length:ℝ)+1) 1 (schwartzWord ws) := coreBound_word ws (by linarith)
  have hd (v : E) : CoreBound ((ws.length:ℝ)+1) 0 (fun f => ∂_{v} (schwartzWord ws f)) :=
    (coreBound_deriv v (s:=1) (t:=0) (by norm_num)).comp hw
  have h1 : CoreBound ((ws.length:ℝ)+1) 0 (fun f =>
      SchwartzMap.smulLeftCLM ℂ (∂_{a} κ : 𝓢(E,ℂ)) (∂_{b} (schwartzWord ws f))) :=
    (coreBound_product_zero (∂_{a} κ)).comp (hd b)
  have h2 : CoreBound ((ws.length:ℝ)+1) 0 (fun f =>
      SchwartzMap.smulLeftCLM ℂ (∂_{b} κ : 𝓢(E,ℂ)) (∂_{a} (schwartzWord ws f))) :=
    (coreBound_product_zero (∂_{b} κ)).comp (hd a)
  have h3 : CoreBound ((ws.length:ℝ)+1) 0 (fun f =>
      SchwartzMap.smulLeftCLM ℂ (∂_{a} (∂_{b} κ) : 𝓢(E,ℂ)) (schwartzWord ws f)) :=
    (coreBound_product_zero (∂_{a} (∂_{b} κ))).comp
      (coreBound_word ws (by linarith : (0:ℝ) ≤ (ws.length:ℝ)+1-ws.length))
  exact (h1.add h2).add h3

lemma UniformSobolev.raise_one {Z : Type*} {s : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F)
    (hD : ∀ j, UniformSobolev s (fun z => ∂_{stdOrthonormalBasis ℝ E j} (F z))) :
    UniformSobolev (s+1) F := by
  obtain ⟨C,hC,hc⟩ := hF
  choose B hB hb using hD
  let c : ℝ := ‖(((2*Real.pi)^2:ℝ):ℂ)⁻¹‖
  refine ⟨‖raiseZero (E:=E) s‖*C+c*∑ j, ‖raiseDeriv s (stdOrthonormalBasis ℝ E j)‖*B j,
    add_nonneg (mul_nonneg (norm_nonneg _) hC)
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hB j))),fun z => ?_⟩
  rw [schwartzCoord_raise_one]
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  apply add_le_add
  · exact ((raiseZero s).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hc z) (norm_nonneg _))
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
      ((raiseDeriv s (stdOrthonormalBasis ℝ E j)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hb j z) (norm_nonneg _))))

lemma UniformSobolev.of_words {Z : Type*} (k : ℕ) {s : ℝ} {F : Z → 𝓢(E,ℂ)}
    (h : ∀ ws : List E, ws.length ≤ k → UniformSobolev s (fun z => schwartzWord ws (F z))) :
    UniformSobolev (s+k) F := by
  induction k generalizing F with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have hv := ih (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (F:=fun z => ∂_{stdOrthonormalBasis ℝ E j} (F z)) (fun ws hw => by
        have hh := h (ws++[stdOrthonormalBasis ℝ E j]) (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
        simpa only [schwartzWord_append,schwartzWord,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply,lineDerivOpCLM_apply] using hh)
    convert hv.raise_one hd using 1
    push_cast
    ring
end SobolevChart

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ}

lemma hessianEntrySchwartz_word (ws : List (EC d)) (i j : Fin d) (f : 𝓢(EC d,ℂ)) :
    hessianEntrySchwartz i j (schwartzWord ws f) = schwartzWord ws (hessianEntrySchwartz i j f) := by
  simp only [hessianEntrySchwartz,smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,map_add,map_smul,schwartzWord_deriv]

def wordHessianError (κ : 𝓢(EC d,ℂ)) (ws : List (EC d)) (i j : Fin d)
    (f : 𝓢(EC d,ℂ)) : 𝓢(EC d,ℂ) :=
  (1/4:ℂ) • (wordSecondError κ ws (hessianDirection i) (hessianDirection j) f +
    wordSecondError κ ws (hessianIDirection i) (hessianIDirection j) f +
    Complex.I • (wordSecondError κ ws (hessianIDirection i) (hessianDirection j) f +
      (-1:ℂ) • wordSecondError κ ws (hessianDirection i) (hessianIDirection j) f))

lemma wordHessianError_identity (κ f : 𝓢(EC d,ℂ)) (ws : List (EC d)) (i j : Fin d) :
    hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws f)) =
      SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws (hessianEntrySchwartz i j f)) +
        wordHessianError κ ws i j f := by
  simp only [hessianEntrySchwartz,wordHessianError,smul_apply,
    add_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,
    wordSecondError_identity,map_add,map_smul]
  module

lemma wordHessianError_bound (κ : 𝓢(EC d,ℂ)) (ws : List (EC d)) (i j : Fin d) :
    CoreBound ((ws.length:ℝ)+1) 0 (wordHessianError κ ws i j) :=
  ((wordSecondError_bound κ ws _ _).add (wordSecondError_bound κ ws _ _) |>.add
    (((wordSecondError_bound κ ws _ _).add ((wordSecondError_bound κ ws _ _).smul (-1))).smul Complex.I)).smul (1/4)
end GlobalElliptic

end
end

end OAI
