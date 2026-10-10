import OAI.Analysis.CircleDomains.Topology.CompactArcWinding
import OAI.Analysis.CircleDomains.Probability.DiskStartLaw

namespace OAI

/-! The bounded-depth part of a compact family of disk rays lies in a
common initial time interval, on which the angular lifts are uniformly bounded. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def puncturedArgument : C({z : ℂ // z ≠ 0}, UnitAddCircle) :=
  ⟨fun z => normalizedArgument z.val, by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_normalizedArgument z.property).comp continuous_subtype_val.continuousAt⟩

theorem compact_disk_rays_uniform_tail
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hend : ∀ γ ∈ K, γ 1 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ c : PathTime, 0 < c ∧ c < 1 ∧
      ∀ γ ∈ K, ∀ t, c ≤ t → ‖γ t‖ < r := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let E : K × PathTime → ℂ := fun p => p.1.val p.2
  have hE : Continuous E := continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hE) r hr
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  let c : PathTime := ⟨1 - d / 2, by constructor <;> linarith⟩
  have hc0 : (0 : PathTime) < c := by
    change (0 : ℝ) < 1 - d / 2
    linarith
  have hc1 : c < 1 := by
    change 1 - d / 2 < (1 : ℝ)
    linarith
  refine ⟨c, hc0, hc1, ?_⟩
  intro γ hγ t ht
  have htd : dist t (1 : PathTime) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(t : ℝ) - 1| < δ
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    have hct : 1 - d / 2 ≤ (t : ℝ) := ht
    have hdδ : d ≤ δ := min_le_left _ _
    change -((t : ℝ) - 1) < δ
    linarith
  have hp : dist ((⟨γ, hγ⟩ : K), t) ((⟨γ, hγ⟩ : K), (1 : PathTime)) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using htd
  simpa only [E, hend γ hγ, dist_zero_right] using hmod hp

theorem compact_disk_rays_initial_angle_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) {r : ℝ} (hr : 0 < r) :
    ∃ (c : PathTime) (hc : c < ⊤) (M : ℝ),
      0 < c ∧
      (∀ γ ∈ K, ∀ t, r ≤ ‖γ t‖ → t < c) ∧
      ∀ γ : K, ∀ t : unitInterval,
        |realCirclePathLift (initialArcAngles puncturedArgument γ.val
          (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) t| ≤ M := by
  obtain ⟨c, hc0, hc1, htail⟩ := compact_disk_rays_uniform_tail K hK
    (fun γ hγ => (hKS hγ).2.2.1) hr
  have hc : c < ⊤ := hc1
  obtain ⟨M, hM⟩ := compact_initial_arc_lifts_bounded K hK 0
    (fun γ hγ => (hKS hγ).1) (fun γ hγ => (hKS hγ).2.2.1)
    puncturedArgument c hc
  refine ⟨c, hc, M, hc0, ?_, hM⟩
  intro γ hγ t ht
  by_contra! hct
  exact (not_lt_of_ge ht) (htail γ hγ t hct)

end CircleDomainRigidity

end

end OAI
