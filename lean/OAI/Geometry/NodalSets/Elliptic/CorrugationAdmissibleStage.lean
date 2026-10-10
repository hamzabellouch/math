import OAI.Geometry.NodalSets.Elliptic.AdmissibilityNeighborhood
import OAI.Geometry.NodalSets.Elliptic.CorrugationGridAdmissibility

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_small_admissible_corrugation (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {U : Set Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:Coord) (1/2))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ) (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∃ e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord,
      let w := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun i ↦ o i+L)) ∧ (∀ x, |w x| < ε) ∧
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
        (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)))) ∧
      ∃ V : Set Coord, IsOpen V ∧ Icc o (fun i ↦ o i+L) ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, metricGradient g (S+w) x ≠ 0 ∧
          ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g (S+w) x) t = 0 ∧
            0 < sourceHessian g (S+w) x (metricGradient g (S+w) x) (metricGradient g (S+w) x) +
              (g x (metricGradient g (S+w) x) (metricGradient g (S+w) x)+4)*sourceHessian g (S+w) x t t := by
  have hn := fun y hy ↦ (hadm y hy).1
  have hadmissible := corrugation_grid_admissibility o hL g S χ hU hDU hg hS hp hsym hadm
    hχsmooth hχsupp hχ0 hχ1 hAχ hχA
  have hχb : ∀ z, |χ z| ≤ 1 := fun z ↦ by rw [abs_of_nonneg (hχ0 z)]; exact hχ1 z
  have hsmall := corrugationEnvelopePerturbation_small o hL g S χ corrugationFixedAmplitude
    hU hDU hg hS hp hn hχsupp hχb hε
  filter_upwards [hadmissible,hsmall] with k hk hs
  obtain ⟨e,he⟩ := exists_corrugation_grid_frames o hL (corrugationSubdivision_positive k)
    g S (fun y hy ↦ hp y (hDU hy)) hsym hadm
  let w := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
  have hw : ContDiff ℝ ∞ w := corrugationEnvelopePerturbation_smooth o L k g S χ corrugationFixedAmplitude e hχsmooth
  have had := hk e (fun i ↦ (he i).1) (fun i ↦ (he i).2.1) (fun i ↦ (he i).2.2.1)
  obtain ⟨V,hV,hDV,hVU,hVa⟩ := source_admissibility_neighborhood g (S+w) hU hDU hg (hS.add hw.contDiffOn) hp had
  refine ⟨e,hw,(corrugationEnvelopePerturbation_support o hL k g S χ corrugationFixedAmplitude e hχsupp).1,
    (corrugationEnvelopePerturbation_support o hL k g S χ corrugationFixedAmplitude e hχsupp).2,
    hs e,?_,V,hV,hDV,hVU,hVa⟩
  intro i
  exact ⟨(he i).1,(he i).2.1,(he i).2.2.1⟩

end
end Yau.Geometry

end OAI
