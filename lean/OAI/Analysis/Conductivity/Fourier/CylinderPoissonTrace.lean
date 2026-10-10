import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CylinderPoissonH1

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def spectralPoissonTrace (s : Fin 3 → ℝ) (R : ℝ)
    (f : spectralTraceGraph (torusRate s)) : spectralTraceGraph (torusRate s) :=
  ⟨WithLp.toLp 2 (fun j => sequenceMultiplier
      (fun h => (Real.exp (-torusRate s h*|R|):ℂ)) 1 zero_le_one
      (poissonMultiplier_bound s R) (f.val j)),by
    intro h
    change (Real.exp (-torusRate s h*|R|):ℂ)*(f.val 1 h)=
      (Real.sqrt (torusRate s h):ℂ)*((Real.exp (-torusRate s h*|R|):ℂ)*(f.val 0 h))
    rw [f.property h]
    ring⟩

lemma spectralTraceSingle_hasSum (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) :
    HasSum (fun h => spectralTraceSingleL s h (f.val 0 h)) f := by
  have hc (j : Fin 2) :
      HasSum (fun h => (spectralTraceSingleL s h (f.val 0 h)).val j) (f.val j) := by
    fin_cases j
    · exact lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 0)
    · have H := lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 1)
      convert H using 1
      · funext h
        change (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*f.val 0 h) : SpectralL2 TorusModes)=lp.single 2 h (f.val 1 h)
        rw [f.property h]
      · rfl
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
        ∑ h∈F,(spectralTraceSingleL s h (f.val 0 h)).val j) atTop
      (𝓝 (fun j => f.val j)) := tendsto_pi_nhds.mpr hc
  have H := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => SpectralL2 TorusModes)).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h∈F,spectralTraceSingleL s h (f.val 0 h)) atTop (𝓝 f)
  apply tendsto_subtype_rng.mpr
  convert H using 1
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,Submodule.coe_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma cylinderPolynomialJetL_single (R : ℝ) (h : TorusModes) (q : smoothComplexAxis) :
    cylinderPolynomialJetL R (Finsupp.single h q)=
      smoothCylinderModeJet (smoothComplexAxis_smooth q) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_single]
  exact cylinderJetMode_smooth _ R h

lemma cylinderPolynomialTraceL_single (s : Fin 3 → ℝ) (t : ℝ) (h : TorusModes)
    (q : smoothComplexAxis) :
    cylinderPolynomialTraceL s t (Finsupp.single h q)=spectralTraceSingleL s h (q t) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_single]
  rfl

lemma endPoissonModeJet_mem_trace_graph (s : Fin 3 → ℝ) {R : ℝ} (_ : 0≤R)
    (h : TorusModes) (a : ℂ) :
    (endPoissonModeJet s R h a,
      (spectralTraceSingleL s h a,
       spectralTraceSingleL s h ((Real.exp (-torusRate s h*R):ℂ)*a)))∈cylinderSobolevGraph s R := by
  apply Submodule.le_topologicalClosure
  refine ⟨Finsupp.single h (⟨axialDecayField (torusRate s h) a,axialDecayField_smooth _ _⟩ : smoothComplexAxis),?_⟩
  apply Prod.ext
  · exact (cylinderPolynomialJetL_single R h _).trans (endPoissonModeJet_smooth s R h a).symm
  · apply Prod.ext
    · change cylinderPolynomialTraceL s 0 _=_
      rw [cylinderPolynomialTraceL_single]
      simp only [axialDecayField,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul]
    · change cylinderPolynomialTraceL s R _=_
      rw [cylinderPolynomialTraceL_single]
      rfl

theorem endPoissonJet_mem_trace_graph (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    (endPoissonJet s hs R hR f,(f,spectralPoissonTrace s R f))∈cylinderSobolevGraph s R := by
  have H := (endPoissonJet_hasSum s hs R hR f).prodMk
    ((spectralTraceSingle_hasSum s f).prodMk (spectralTraceSingle_hasSum s (spectralPoissonTrace s R f)))
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto H
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  change (endPoissonModeJet s R h (f.val 0 h),
    (spectralTraceSingleL s h (f.val 0 h),spectralTraceSingleL s h
      ((Real.exp (-torusRate s h*|R|):ℂ)*(f.val 0 h))))∈cylinderSobolevGraph s R
  rw [abs_of_nonneg hR]
  exact endPoissonModeJet_mem_trace_graph s hR h _

end ScalarConductivity

end

end OAI
