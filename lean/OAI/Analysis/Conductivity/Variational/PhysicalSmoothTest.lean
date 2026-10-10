import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalChildIntegral
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def piSmoothH1 {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) : H1 :=
  smoothH1 (φ ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)))
    (hφ.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma piSmoothH1_jet {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (piSmoothH1 hφ).val=ᵐ[ballMeasure] (fun x => piSmoothJet φ (WithLp.ofLp x)) := by
  filter_upwards [(smoothJet_memLp
    (hφ.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).coeFn_toLp]
    with x hx
  change (piSmoothH1 hφ).val x=_ at hx
  rw [hx]
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  change gradient (φ ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))) x j=
    fderiv ℝ φ (WithLp.ofLp x) (Pi.single j 1)
  rw [gradient_apply_single,fderiv_comp x (hφ.differentiable (by simp) _)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).differentiableAt]
  rw [ContinuousLinearEquiv.fderiv]
  rfl

lemma piSmoothH1_gradient {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {D : Set (Fin 3 → ℝ)} (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient (piSmoothH1 hφ) y=physicalTestCovector φ y := by
  apply originalPiGradient_eq_on_ball hb (piSmoothH1 hφ) _
  filter_upwards [piSmoothH1_jet hφ] with x hx _ j
  exact congrArg (fun v : JetFiber => v j.succ) hx

def physicalSmoothCentral {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) : centralEnergySpace s :=
  ⟨centralEmbedL s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩,
    (Submodule.le_topologicalClosure _) ⟨_,rfl⟩⟩

lemma physicalSmoothCentral_jet {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    H1JetOn (piSmoothH1 hφ) centralPhysical (centralFullJetCLM s (physicalSmoothCentral s hφ).val) := by
  let f : centralSmoothFunctions := ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩
  have he : (fun y => f (sourcePairCoordinates y))=φ := by
    funext y
    exact congrArg φ (sourcePairCLE.symm_apply_apply y)
  filter_upwards [piSmoothH1_jet hφ,centralFullJetCLM_smooth_ae s f] with x hx hc hy
  change _=centralFullJetCLM s (centralEmbedL s f) x
  rw [hc hy,he,hx]

lemma physicalSmoothCentral_parent_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    centralT s 0 (physicalSmoothCentral s hφ)=smoothCollarTrace s centralThickness hφ := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ 0).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1

lemma physicalSmoothCentral_child_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    centralT s k.succ (physicalSmoothCentral s hφ)=smoothCollarTrace s (-centralThickness)
      (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ k.succ).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1
  funext θ
  fin_cases k <;> rfl

lemma physicalTestCovector_child {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (σ : ℝ) (y : Fin 3 → ℝ) :
    physicalTestCovector (φ ∘ sourceChildCoordinates σ) y=
      (fun i => sourceScale*physicalTestCovector φ (sourceChildCoordinates σ y) (childAxis i)) := by
  ext i
  change fderiv ℝ (φ ∘ sourceChildCoordinates σ) y (Pi.single i 1)=_
  rw [((hφ.differentiable (by simp) _).hasFDerivAt.comp y
    (sourceChildCoordinates_hasFDeriv σ y)).fderiv,ContinuousLinearMap.comp_apply]
  have he : sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [sourceChildDerivative_apply,childAxis]
  rw [he,map_smul]
  rfl

end ScalarConductivity

end
end

end OAI
