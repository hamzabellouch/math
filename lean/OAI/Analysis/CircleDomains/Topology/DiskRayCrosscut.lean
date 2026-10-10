import OAI.Analysis.CircleDomains.Topology.CompactifiedDiskRay

namespace OAI

/-! The compactified lifted ray is a simple crosscut of the closed disk. -/

open Set Function
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem diskRayComplex_injective (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Injective (diskRayComplex γ hi he) := by
  intro s t h
  apply diskRayLift_injective γ hi he
  apply Prod.ext
  · simpa [diskRayComplex, diskRayLift] using congrArg Complex.re h
  · simpa only [diskRayLift, ContinuousMap.coe_mk, diskRayComplex_im] using congrArg Complex.im h

theorem compactifiedDiskRay_injective {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    Injective (compactifiedDiskRay γ hγ.1 hγ.2.2.1) := by
  intro s t h
  have hnonneg (u : DiskRayTime) : 0 ≤ (diskRayComplex γ hγ.1 hγ.2.2.1 u).im := by
    simpa only [diskRayComplex_im] using diskRayDepth_nonneg hγ u
  by_cases hs : s < ⊤
  · by_cases ht : t < ⊤
    · rw [compactifiedDiskRay, dite_eq_left hs, compactifiedDiskRay, dite_eq_left ht] at h
      have he := halfPlaneDisk_injOn (hnonneg ⟨s, hs⟩) (hnonneg ⟨t, ht⟩) h
      exact congrArg Subtype.val (diskRayComplex_injective γ hγ.1 hγ.2.2.1 he)
    · rw [compactifiedDiskRay, dite_eq_left hs, compactifiedDiskRay, dite_eq_right ht] at h
      exact (halfPlaneDisk_ne_one (hnonneg ⟨s, hs⟩) h).elim
  · by_cases ht : t < ⊤
    · rw [compactifiedDiskRay, dite_eq_right hs, compactifiedDiskRay, dite_eq_left ht] at h
      exact (halfPlaneDisk_ne_one (hnonneg ⟨t, ht⟩) h.symm).elim
    · exact (top_le_iff.mp (not_lt.mp hs)).trans (top_le_iff.mp (not_lt.mp ht)).symm

theorem compactifiedDiskRay_start_norm {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    ‖compactifiedDiskRay γ hγ.1 hγ.2.2.1 ⊥‖ = 1 := by
  rw [compactifiedDiskRay, dite_eq_left bot_lt_top]
  apply halfPlaneDisk_norm_eq
  simp only [diskRayComplex_im, diskRayDepth]
  change -Real.log ‖γ 0‖ = 0
  rw [hγ.2.1, Real.log_one, neg_zero]

theorem compactifiedDiskRay_start_ne_one {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    compactifiedDiskRay γ hγ.1 hγ.2.2.1 ⊥ ≠ 1 := by
  rw [← compactifiedDiskRay_top γ hγ.1 hγ.2.2.1]
  exact fun h => bot_ne_top ((compactifiedDiskRay_injective hγ) h)

theorem compactifiedDiskRay_interior {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet)
    (t : PathTime) (ht : t ∈ Ioo ⊥ ⊤) :
    ‖compactifiedDiskRay γ hγ.1 hγ.2.2.1 t‖ < 1 := by
  rw [compactifiedDiskRay, dite_eq_left ht.2]
  apply halfPlaneDisk_norm_lt
  rw [diskRayComplex_im]
  have hp : 0 < ‖γ t‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ hγ.1 hγ.2.2.1 ⟨t, ht.2⟩)
  have hn : ‖γ t‖ < 1 := hγ.2.2.2 t ht
  have hl := Real.log_lt_log hp hn
  rw [Real.log_one] at hl
  exact neg_pos.mpr hl

def compactifiedRayPath (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) : C(PathTime, ℂ) :=
  ⟨compactifiedDiskRay γ hγ.1 hγ.2.2.1, continuous_compactifiedDiskRay hγ⟩

end CircleDomainRigidity

end

end OAI
