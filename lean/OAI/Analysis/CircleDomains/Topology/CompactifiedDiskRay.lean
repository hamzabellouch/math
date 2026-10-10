import OAI.Analysis.CircleDomains.Topology.DiskRayClosed
import OAI.Analysis.CircleDomains.Topology.HalfPlaneDisk

namespace OAI

/-! A proper lifted ray compactifies to a disk crosscut. The endpoint at
infinity is added using the quantitative Cayley estimate. -/

open Set Function Filter Metric
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

def diskRayComplex (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    C(DiskRayTime, ℂ) :=
  ⟨fun t => (diskRayAngle γ hi he t : ℂ) + (diskRayDepth γ t : ℂ) * Complex.I,
    ((Complex.continuous_ofReal.comp (continuous_diskRayAngle γ hi he)).add
      ((Complex.continuous_ofReal.comp (continuous_diskRayDepth γ hi he)).mul continuous_const))⟩

@[simp] theorem diskRayComplex_im (γ : C(PathTime, ℂ)) (hi : Injective γ)
    (he : γ ⊤ = 0) (t : DiskRayTime) :
    (diskRayComplex γ hi he t).im = diskRayDepth γ t := by
  simp [diskRayComplex]

def compactifiedDiskRay (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : PathTime) : ℂ :=
  if ht : t < ⊤ then halfPlaneDisk (diskRayComplex γ hi he ⟨t, ht⟩) else 1

@[simp] theorem compactifiedDiskRay_top (γ : C(PathTime, ℂ)) (hi : Injective γ)
    (he : γ ⊤ = 0) : compactifiedDiskRay γ hi he ⊤ = 1 := by
  simp only [compactifiedDiskRay, lt_self_iff_false, dite_false]

theorem continuousOn_compactifiedDiskRay {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    ContinuousOn (compactifiedDiskRay γ hγ.1 hγ.2.2.1) (Iio ⊤) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h := continuousOn_halfPlaneDisk.comp_continuous
    (diskRayComplex γ hγ.1 hγ.2.2.1).continuous
    (fun t => by
      change 0 ≤ (diskRayComplex γ hγ.1 hγ.2.2.1 t).im
      rw [diskRayComplex_im]
      exact diskRayDepth_nonneg hγ t)
  apply h.congr
  intro t
  change halfPlaneDisk (diskRayComplex γ hγ.1 hγ.2.2.1 t) =
    compactifiedDiskRay γ hγ.1 hγ.2.2.1 t.val
  symm
  unfold compactifiedDiskRay
  rw [dite_eq_left t.property]

theorem continuousAt_compactifiedDiskRay_top {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    ContinuousAt (compactifiedDiskRay γ hγ.1 hγ.2.2.1) ⊤ := by
  rw [ContinuousAt, compactifiedDiskRay_top]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c, _, hc, htail⟩ := compact_disk_rays_depth_escape {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) (2 / ε)
  filter_upwards [Ioi_mem_nhds (show c < (⊤ : PathTime) from hc)] with t ht
  by_cases htt : t < ⊤
  · rw [compactifiedDiskRay, dite_eq_left htt]
    have hy : 2 / ε < diskRayDepth γ ⟨t, htt⟩ :=
      htail γ (mem_singleton γ) ⟨t, htt⟩ ht.le
    have hpos : 0 < diskRayDepth γ ⟨t, htt⟩ + 1 :=
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (diskRayDepth_nonneg hγ _))
    apply (halfPlaneDisk_dist_one_le (by
      simpa only [diskRayComplex_im] using diskRayDepth_nonneg hγ ⟨t, htt⟩)).trans_lt
    rw [diskRayComplex_im]
    apply (div_lt_iff₀ hpos).mpr
    have hy' : 2 < diskRayDepth γ ⟨t, htt⟩ * ε := (div_lt_iff₀ hε).mp hy
    nlinarith
  · simp only [compactifiedDiskRay, htt, dite_false, dist_self, hε]

theorem continuous_compactifiedDiskRay {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    Continuous (compactifiedDiskRay γ hγ.1 hγ.2.2.1) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t < ⊤
  · exact (continuousOn_compactifiedDiskRay hγ).continuousAt (isOpen_Iio.mem_nhds ht)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    exact continuousAt_compactifiedDiskRay_top hγ

end CircleDomainRigidity

end

end OAI
