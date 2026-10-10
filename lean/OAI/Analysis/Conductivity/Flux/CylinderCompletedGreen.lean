import Mathlib
import OAI.Analysis.Conductivity.Flux.CylinderSeriesGreen
import OAI.Analysis.Conductivity.Sobolev.CylinderSobolevGraph

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def spectralWeightedPairL (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes) :
    spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (innerSL ℂ g).comp ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 1).comp
    (spectralTraceGraph (torusRate s)).subtypeL)

def spectralEndWeight (s : Fin 3 → ℝ) (R : ℝ) (f : spectralTraceGraph (torusRate s)) :
    SpectralL2 TorusModes :=
  sequenceMultiplier (fun h => (Real.exp (-torusRate s h*|R|):ℂ)) 1
    zero_le_one (poissonMultiplier_bound s R) (f.val 1)

lemma spectralWeightedPair_single (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes)
    (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s g (spectralTraceSingleL s h a)=
      inner ℂ (g h) ((Real.sqrt (torusRate s h):ℂ)*a) := by
  change inner ℂ g (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*a))=_
  exact lp.inner_single_right h _ g

lemma spectralWeightedPair_initial (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s (f.val 1) (spectralTraceSingleL s h a)=
      (torusRate s h:ℂ)*inner ℂ (f.val 0 h) a := by
  rw [spectralWeightedPair_single,f.property h]
  have he : (Real.sqrt (torusRate s h):ℂ)^2=(torusRate s h:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤torusRate s h from Real.sqrt_nonneg _)
  simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal]
  calc
    _=(Real.sqrt (torusRate s h):ℂ)^2*(starRingEnd ℂ (f.val 0 h)*a) := by ring
    _=_ := by rw [he]; ring

lemma spectralWeightedPair_terminal (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    {R : ℝ} (hR : 0≤R) (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s (spectralEndWeight s R f) (spectralTraceSingleL s h a)=
      (torusRate s h*Real.exp (-torusRate s h*R):ℝ)*inner ℂ (f.val 0 h) a := by
  rw [spectralWeightedPair_single]
  change inner ℂ ((Real.exp (-torusRate s h*|R|):ℂ)*(f.val 1 h)) _=_
  rw [abs_of_nonneg hR]
  change inner ℂ ((Real.exp (-torusRate s h*R):ℂ) • (f.val 1 h)) _=_
  rw [inner_smul_left]
  rw [←spectralWeightedPair_single,spectralWeightedPair_initial]
  simp only [Complex.conj_ofReal,Complex.ofReal_mul]
  ring

lemma spectralWeightedPair_polynomial (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes)
    (t : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    spectralWeightedPairL s g (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,spectralWeightedPairL s g (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem flatCylinder_completed_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s))
    (z : cylinderSobolevGraph s R) :
    flatCylinderEnergy s (endPoissonJet s hs R hR.le f) z.val.1=
      spectralWeightedPairL s (f.val 1) z.val.2.1-
        spectralWeightedPairL s (spectralEndWeight s R f) z.val.2.2 := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (flatCylinderEnergyRightCLM s (endPoissonJet s hs R hR.le f)).comp J-
    (((spectralWeightedPairL s (f.val 1)).comp T₀)-
      ((spectralWeightedPairL s (spectralEndWeight s R f)).comp T₁))
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change flatCylinderEnergy s (endPoissonJet s hs R hR.le f) (cylinderPolynomialJetL R p)-
      (spectralWeightedPairL s (f.val 1) (cylinderPolynomialTraceL s 0 p)-
        spectralWeightedPairL s (spectralEndWeight s R f) (cylinderPolynomialTraceL s R p))=0
    rw [cylinderPolynomialJetL_apply,flatCylinder_series_polynomial_green,
      spectralWeightedPair_polynomial,spectralWeightedPair_polynomial]
    simp only [spectralWeightedPair_initial,spectralWeightedPair_terminal s f hR.le,Finset.sum_sub_distrib]
    ring
  have hz := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property
  exact sub_eq_zero.mp hz

theorem cylinderH1_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) (u : cylinderH1Space R) :
    ∃! z : cylinderSobolevGraph s R,
      cylinderSobolevJetCLM s R z=u.val ∧
      flatCylinderEnergy s (endPoissonJet s hs R hR.le f) u.val=
        spectralWeightedPairL s (f.val 1) z.val.2.1-
          spectralWeightedPairL s (spectralEndWeight s R f) z.val.2.2 := by
  obtain ⟨z,hz,hu⟩ := cylinderH1_unique_trace_graph s hR u
  refine ⟨z,⟨hz,?_⟩,fun y hy => hu y hy.1⟩
  rw [←hz]
  exact flatCylinder_completed_green s hs hR f z

end ScalarConductivity

end

end OAI
