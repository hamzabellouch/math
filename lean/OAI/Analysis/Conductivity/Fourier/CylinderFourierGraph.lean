import Mathlib
import OAI.Analysis.Conductivity.Fourier.CylinderPoissonTrace
import OAI.Analysis.Conductivity.Fourier.CylinderFourierComplete

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderJetCoefficient (R : ℝ) (J : FiniteCylinderJets R) (h : TorusModes) : FiniteAxisJets R :=
  WithLp.toLp 2 (fun j => cylinderCoefficientLp (J j) h)

lemma cylinderJetCoefficient_hasSum (R : ℝ) (J : FiniteCylinderJets R) :
    HasSum (fun h => cylinderJetMode R h (cylinderJetCoefficient R J h)) J := by
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
      ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h) j)
      atTop (𝓝 (fun j => J j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact cylinderCoefficient_hasSum (J j)
  have hmap := (PiLp.continuous_toLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h)) atTop _
  convert hmap using 1
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]

theorem cylinderH1_of_smooth_coefficients (R : ℝ) (J : FiniteCylinderJets R)
    (q : TorusModes → smoothComplexAxis)
    (hq : ∀ h,cylinderJetCoefficient R J h=smoothAxisModeJet (smoothComplexAxis_smooth (q h)) R h) :
    J∈cylinderH1Space R := by
  have hsum := cylinderJetCoefficient_hasSum R J
  simp only [hq,cylinderJetMode_smooth] at hsum
  apply mem_closure_of_tendsto hsum
  apply Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  exact ⟨Finsupp.single h (q h),cylinderPolynomialJetL_single R h (q h)⟩

theorem cylinderGraph_of_smooth_coefficients (s : Fin 3 → ℝ) (R : ℝ)
    (J : FiniteCylinderJets R) (q : TorusModes → smoothComplexAxis)
    (hq : ∀ h,cylinderJetCoefficient R J h=smoothAxisModeJet (smoothComplexAxis_smooth (q h)) R h)
    (f₀ f₁ : spectralTraceGraph (torusRate s))
    (hf₀ : ∀ h,f₀.val 0 h=q h 0) (hf₁ : ∀ h,f₁.val 0 h=q h R) :
    (J,(f₀,f₁))∈cylinderSobolevGraph s R := by
  classical
  have hsum := cylinderJetCoefficient_hasSum R J
  simp only [hq,cylinderJetMode_smooth] at hsum
  have hg := hsum.prodMk ((spectralTraceSingle_hasSum s f₀).prodMk (spectralTraceSingle_hasSum s f₁))
  apply mem_closure_of_tendsto hg
  apply Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  refine ⟨Finsupp.single h (q h),?_⟩
  change (cylinderPolynomialJetL R (Finsupp.single h (q h)),
      (cylinderPolynomialTraceL s 0 (Finsupp.single h (q h)),
      cylinderPolynomialTraceL s R (Finsupp.single h (q h))))=_
  rw [cylinderPolynomialJetL_single,cylinderPolynomialTraceL_single,cylinderPolynomialTraceL_single,hf₀,hf₁]

end ScalarConductivity

end
end

end OAI
