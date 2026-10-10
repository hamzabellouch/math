import OAI.Geometry.NodalSets.Elliptic.CorrugationGridAssembly
import OAI.Geometry.NodalSets.Elliptic.CorrugationNonvanishing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationEnvelopePerturbation (o : Coord) (L : ℝ) (k : ℕ)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord) : Coord → ℝ :=
  corrugationGridSum o L (corrugationSubdivision k) χ amp (corrugationFrequency k)
    (fun i ↦ corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) e

theorem corrugation_grid_nonvanishing (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {U : Set Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:Coord) (1/2)) (amp : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord,
      (∀ i, e i (Pi.single 0 1) =
        (corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i))⁻¹ •
          metricGradient g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) →
      (∀ i a b, g (corrugationCubeCenter o L (corrugationSubdivision k) i)
        (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) →
      ∀ x ∈ Icc o (fun i ↦ o i+L),
        metricGradient g (S+corrugationEnvelopePerturbation o L k g S χ amp e) x ≠ 0 := by
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall (0:Coord) (1/2)).of_isClosed_subset isClosed_closure
      (hχsupp.trans ball_subset_closedBall)
  have hevent := corrugation_local_nonvanishing g S χ isCompact_Icc (convex_Icc o (fun i ↦ o i+L))
    hU hDU hg hS hp hn hχ hc amp hL
  filter_upwards [hevent] with k hk
  intro e he0 he x hx
  let n := corrugationSubdivision k
  let y := corrugationCubeCenter o L n
  let s := fun i ↦ corrugationOldSlope g S (y i)
  let w := fun i ↦ localizedCorrugation χ (corrugationPeriodicWell amp) (s i)
    (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector (e i) 2)
    (frozenFrameCovector (e i) 3) (y i)
  have hR := corrugationScale_positive hL k
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin 4 → Fin n)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)) := by
    intro i _ j _ hij
    exact (corrugationCube_balls_disjoint o hL (corrugationSubdivision_positive k) i j hij).mono
      (localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _)
      (localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _)
  have hsum : corrugationEnvelopePerturbation o L k g S χ amp e =
      (fun z ↦ ∑ i ∈ (Finset.univ : Finset (Fin 4 → Fin n)), w i z) := rfl
  by_cases hactive : ∃ i : Fin 4 → Fin n, x ∈ tsupport (w i)
  · obtain ⟨i,hi⟩ := hactive
    have heq := finite_disjoint_sum_eventually Finset.univ w hd (Finset.mem_univ i) hi
    rw [← hsum] at heq
    have heq' : S+corrugationEnvelopePerturbation o L k g S χ amp e =ᶠ[𝓝 x] S+w i :=
      Filter.EventuallyEq.add Filter.EventuallyEq.rfl heq
    have hy : y i ∈ Icc o (fun j ↦ o j+L) :=
      corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i
    have hxy : ‖x-y i‖ ≤ corrugationScale L k := by
      have hh := localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _ hi
      rw [mem_ball,dist_eq_norm] at hh
      linarith
    have hnlocal := hk (y i) hy x hx hxy (e i) (he0 i) (he i)
    have hgrad : metricGradient g (S+corrugationEnvelopePerturbation o L k g S χ amp e) x =
        metricGradient g (S+w i) x := by
      unfold metricGradient
      rw [heq'.fderiv_eq]
    rw [hgrad]
    exact hnlocal
  · have hzero : corrugationEnvelopePerturbation o L k g S χ amp e =ᶠ[𝓝 x] 0 := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      rw [hsum]
      intro hmem
      have hsupp := finite_sum_support_subset Finset.univ w {z | ∃ i, z ∈ tsupport (w i)}
        (fun i _ z hz ↦ ⟨i,hz⟩)
      exact hactive (hsupp hmem)
    have heq : S+corrugationEnvelopePerturbation o L k g S χ amp e =ᶠ[𝓝 x] S := by
      simpa using Filter.EventuallyEq.add (Filter.EventuallyEq.rfl (f := S)) hzero
    have hgrad : metricGradient g (S+corrugationEnvelopePerturbation o L k g S χ amp e) x =
        metricGradient g S x := by
      unfold metricGradient
      rw [heq.fderiv_eq]
    rw [hgrad]
    exact hn x hx

end
end Yau.Geometry

end OAI
