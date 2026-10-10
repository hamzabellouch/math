import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseNeighborhood
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! A compact good-phase condition persists under a uniform two-jet perturbation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

def secondTensorFromJet (J : RealTwoJet) : Fin 3 → RVec 4 :=
  ![realNormalPart (J 0) (J 1) (J 2), realNormalPart (J 0) (J 1) (J 3),
    realNormalPart (J 0) (J 1) (J 4)]

@[simp] lemma secondTensorFromJet_realTwoJet (F : RField 4) (p : Base) :
    secondTensorFromJet (realTwoJet F p) = realSecondTensor F p := rfl

lemma contDiffAt_secondTensorFromJet {J : RealTwoJet}
    (hJ : NormalFrame.gramDet (J 0) (J 1) ≠ 0) :
    ContDiffAt ℝ ∞ secondTensorFromJet J := by
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : RealTwoJet => K i) J :=
    (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] RVec 4).contDiff.contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 2) hJ
  · exact contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 3) hJ
  · exact contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 4) hJ

def goodJetPhase : Set (RealTwoJet × Base) :=
  {z | NormalFrame.gramDet (z.1 0) (z.1 1) ≠ 0 ∧ Good (secondTensorFromJet z.1) z.2}

lemma isOpen_goodJetPhase : IsOpen goodJetPhase := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hd : Continuous (fun w : RealTwoJet × Base =>
      NormalFrame.gramDet (w.1 0) (w.1 1)) := by
    unfold NormalFrame.gramDet dotProduct
    fun_prop
  have hb : ContinuousAt (fun w : RealTwoJet × Base => secondTensorFromJet w.1) z :=
    (contDiffAt_secondTensorFromJet hz.1).continuousAt.comp continuous_fst.continuousAt
  exact (hd.continuousAt.eventually_ne hz.1).and
    (good_eventually hb continuous_snd.continuousAt hz.2)

/-- The radius depends on the fixed immersion, phase and compact set, and is
independent of all higher derivatives of the perturbed map. -/
theorem compact_good_phase_stability {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : TopologicalSpace.Compacts Base)
    (hImm : ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ (K : Set Base), Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ G : RField 4,
      (∀ p ∈ (K : Set Base), ‖realTwoJet G p - realTwoJet F p‖ < ε) →
      ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ G p) ∧
        Good (realSecondTensor G p) (phaseDerivative φ p) := by
  let J : Base → RealTwoJet × Base := fun p => (realTwoJet F p,phaseDerivative φ p)
  have hJ : Continuous J := (contDiff_realTwoJet hF).continuous.prodMk (continuous_phaseDerivative hφ)
  have hc : IsCompact (J '' (K : Set Base)) := K.isCompact.image hJ
  have hj : J '' (K : Set Base) ⊆ goodJetPhase := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨gramDet_ne_zero_of_injective _ (hImm p hp),hgood p hp⟩
  obtain ⟨ε,hε,he⟩ := hc.exists_thickening_subset_open isOpen_goodJetPhase hj
  refine ⟨ε,hε,?_⟩
  intro G hGF p hp
  have hdist : dist (realTwoJet G p,phaseDerivative φ p) (J p) < ε := by
    dsimp only [J]
    rw [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)]
    simpa only [dist_eq_norm] using hGF p hp
  have hmem : (realTwoJet G p,phaseDerivative φ p) ∈ goodJetPhase :=
    he (Metric.mem_thickening_iff.mpr ⟨J p,mem_image_of_mem J hp,hdist⟩)
  exact ⟨injective_of_gramDet_ne_zero _ hmem.1,hmem.2⟩

end ClosedSurfaceR4.RealModes

end

end OAI
