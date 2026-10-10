import OAI.Geometry.SurfaceImmersion.Correction.UniformRealModeCoefficients
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Fixed compact admissible jet neighborhoods for nearby immersed maps. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def admissibleRealJets : Set RealTwoJet :=
  {J | NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ realNormalPart (J 0) (J 1) (J 4) ≠ 0}

lemma admissibleRealJets_domain : RealJetDomain admissibleRealJets := by
  refine ⟨?_,fun _ h => h.1,fun _ h => h.2⟩
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hs (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : RealTwoJet => K i) J :=
    (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] RVec 4).contDiff.contDiffAt
  have hd : Continuous (fun K : RealTwoJet => NormalFrame.gramDet (K 0) (K 1)) := by
    unfold NormalFrame.gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_realNormalPart (hs 0) (hs 1) (hs 4) hJ.1).continuousAt.eventually_ne hJ.2)

theorem compact_real_jet_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : TopologicalSpace.Compacts Base)
    (hD : ∀ p ∈ (K : Set Base),
      NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ p ∈ (K : Set Base), realSecond F p ≠ 0) :
    ∃ (ε : ℝ) (Q : Set RealTwoJet), 0 < ε ∧ IsCompact Q ∧ Q ⊆ admissibleRealJets ∧
      ∀ G : RField 4, (∀ p ∈ (K : Set Base), ‖realTwoJet G p - realTwoJet F p‖ < ε) →
        MapsTo (realTwoJet G) K Q := by
  let J := realTwoJet F '' (K : Set Base)
  have hJ : IsCompact J := K.isCompact.image (contDiff_realTwoJet hF).continuous
  have hJa : J ⊆ admissibleRealJets := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨hD p hp,hB p hp⟩
  obtain ⟨ε,hε,he⟩ := hJ.exists_cthickening_subset_open admissibleRealJets_domain.isOpen hJa
  refine ⟨ε,Metric.cthickening ε J,hε,hJ.cthickening,he,?_⟩
  intro G hGF p hp
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  exact ⟨realTwoJet F p,mem_image_of_mem _ hp,by simpa only [dist_eq_norm] using hGF p hp⟩

/-- The coefficient constant is fixed before the nearby map. Only its displayed
weighted two-jet bound enters the estimate. -/
theorem RealModeDomain.uniform_compact_reconstruction {F : RField 4}
    (hF : ContDiff ℝ ∞ F) {Ω U : Set Base} (h : RealModeDomain F Ω)
    (hU : IsOpen U) (K : TopologicalSpace.Compacts Base)
    (hUK : U ⊆ K) (hKΩ : (K : Set Base) ⊆ Ω) (m : ℕ) :
    ∃ ε D : ℝ, 0 < ε ∧ 1 ≤ D ∧ ∀ (G : RField 4) (s C : ℝ),
      ContDiff ℝ ∞ G →
      (∀ p ∈ (K : Set Base), ‖realTwoJet G p - realTwoJet F p‖ < ε) →
      0 < s → 1 ≤ C → WeightedBound U s m C (realTwoJet G) →
      ReconstructionCoefficientBound (fun p => complexify (G p)) U s m
        ((m.factorial : ℝ) * D * C^m) := by
  obtain ⟨ε,Q,hε,hQ,hQa,hclose⟩ := compact_real_jet_neighborhood hF K
    (fun p hp => h.determinant p (hKΩ hp)) (fun p hp => h.good p (hKΩ hp))
  obtain ⟨D,hD,hd⟩ := compact_real_reconstruction_bounds hU admissibleRealJets_domain hQ hQa m
  refine ⟨ε,D,hε,hD,?_⟩
  intro G s C hG hGF hs hC hb
  exact hd G s C hs hC hG (fun p hp => hclose G hGF (hUK hp)) hb

end ClosedSurfaceR4.RealModes

end

end OAI
