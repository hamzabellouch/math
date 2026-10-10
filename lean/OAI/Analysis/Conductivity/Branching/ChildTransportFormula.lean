import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildH10Transport

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childTransportComponentCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) (i : Fin 4) :
    childTransportComponentCLM k i z=ᵐ[volume] (fun y => Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm y) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis j).succ) i) := by
  have hc (j : Fin 4) : ballWholePiComponentCLM j z=ᵐ[volume] (fun y => f y j) := by
    filter_upwards [ballWholePiComponentCLM_ae j z,he] with y hi hy
    rw [hi,hy]
  have hp (j : Fin 4) := (sourceChildPushforwardCLM_ae (actualChildSign k) (ballWholePiComponentCLM j z)).trans
    ((sourceChildInverse_quasi _).ae_eq_comp (hc j))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp 0
  · apply (Lp.coeFn_smul _ _).trans
    filter_upwards [hp (childAxis j).succ] with y hy
    exact congrArg (fun t : ℝ => sourceScale⁻¹*t) hy

lemma childTransportJetCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) :
    childTransportJetCLM k z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j).succ))) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childTransportComponentCLM_ae_of_ae k z f he i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i z),ae_all_iff.mpr hi] with x hx hi
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i z) x=_
  rw [hx]
  ext i
  exact hi i

lemma childAxis_involutive (i : Fin 3) : childAxis (childAxis i)=i := by
  fin_cases i <;> rfl

lemma sourceChildDerivative_single (i : Fin 3) :
    sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
  rw [sourceChildDerivative_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff]

lemma physical_child_partial_cancel {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (σ : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) :
    sourceScale⁻¹*fderiv ℝ (q ∘ sourceChildCoordinates σ)
      ((sourceChildHomeomorph σ).symm y) (Pi.single (childAxis i) 1)=
        fderiv ℝ q y (Pi.single i 1) := by
  have hD := ((hq.differentiable (by simp)) _).hasFDerivAt.comp
    ((sourceChildHomeomorph σ).symm y) (sourceChildCoordinates_hasFDeriv σ _)
  rw [hD.fderiv,ContinuousLinearMap.comp_apply,sourceChildDerivative_single,
    childAxis_involutive,map_smul,smul_eq_mul]
  change sourceScale⁻¹*(sourceScale*fderiv ℝ q
    ((sourceChildHomeomorph σ) ((sourceChildHomeomorph σ).symm y)) (Pi.single i 1))=_
  rw [Homeomorph.apply_symm_apply]
  rw [←mul_assoc,inv_mul_cancel₀ (by norm_num [sourceScale]),one_mul]

end ScalarConductivity

end

end OAI
