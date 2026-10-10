import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI


noncomputable section
namespace InjectiveLinearLift
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [T2Space F]

def continuousLift (i : E →L[𝕜] F) (hi : Function.Injective i)
    (j : G →L[𝕜] F) (h : ∀ g, ∃ e, i e = j g) : G →L[𝕜] E := by
  let l := lift i.toLinearMap hi j.toLinearMap h
  apply ContinuousLinearMap.ofIsClosedGraph (g := l)
  have he : (l.graph : Set (G × E)) = {p | i p.2 = j p.1} := by
    ext p
    change p.2 = l p.1 ↔ i p.2 = j p.1
    constructor
    · intro hp
      rw [hp]
      exact lift_spec i.toLinearMap hi j.toLinearMap h p.1
    · intro hp
      apply hi
      exact hp.trans (lift_spec i.toLinearMap hi j.toLinearMap h p.1).symm
  rw [he]
  exact isClosed_eq (i.continuous.comp continuous_snd) (j.continuous.comp continuous_fst)

lemma continuousLift_spec (i : E →L[𝕜] F) (hi : Function.Injective i)
    (j : G →L[𝕜] F) (h : ∀ g, ∃ e, i e = j g) (g : G) :
    i (continuousLift i hi j h g) = j g :=
  lift_spec i.toLinearMap hi j.toLinearMap h g
end InjectiveLinearLift


namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def localSolutionSpace (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) :
    Submodule ℂ (H E F 1 × H E F n) :=
  ⨅ (g : 𝓢(E,ℂ)) (_ : HasCompactSupport (g : E → ℂ)) (_ : tsupport g ⊆ U),
    LinearMap.ker ((smulLeftCLM F g).comp
      ((P.comp (toDistribution E F 1)).comp (ContinuousLinearMap.fst ℂ _ _) -
       (toDistribution E F n).comp (ContinuousLinearMap.snd ℂ _ _))).toLinearMap

lemma mem_localSolutionSpace_iff (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : H E F 1 × H E F n) :
    u ∈ localSolutionSpace U n P ↔
      ∀ (g : 𝓢(E,ℂ)), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
        smulLeftCLM F g (P (toDistribution E F 1 u.1)) =
        smulLeftCLM F g (toDistribution E F n u.2) := by
  simp only [localSolutionSpace,Submodule.mem_iInf,LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    sub_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',map_sub,sub_eq_zero]

instance localSolutionSpace_complete (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) : CompleteSpace (localSolutionSpace U n P) := by
  have h : _root_.IsClosed (↑(localSolutionSpace U n P) : Set (H E F 1 × H E F n)) := by
    unfold localSolutionSpace
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun g => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      ContinuousLinearMap.isClosed_ker _
  exact h.completeSpace_coe

def interiorLift (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (g : 𝓢(E,ℂ))
    (h : ∀ u : localSolutionSpace U n P,
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1))) :
    localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2) := by
  let j : localSolutionSpace U n P →L[ℂ] 𝓢'(E,F) := (smulLeftCLM F g).comp ((toDistribution E F 1).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (localSolutionSpace U n P).subtypeL))
  refine InjectiveLinearLift.continuousLift (toDistribution E F ((n:ℝ)+2))
    (toDistribution_injective ((n:ℝ)+2)) j (fun u => ?_)
  change j u ∈ Set.range (toDistribution E F ((n:ℝ)+2))
  rw [range_toDistribution]
  exact h u

lemma interiorLift_spec (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (g : 𝓢(E,ℂ))
    (h : ∀ u : localSolutionSpace U n P,
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1)))
    (u : localSolutionSpace U n P) :
    toDistribution E F ((n:ℝ)+2) (interiorLift U n P g h u) =
      smulLeftCLM F g (toDistribution E F 1 u.val.1) :=
  InjectiveLinearLift.continuousLift_spec _ _ _ _ _
end TamingCompatibility.HilbertSobolev

end

end OAI
