import OAI.Analysis.CircleDomains.Topology.DiskRayLift

namespace OAI

/-! Different integer translates of a lifted simple disk arc are disjoint. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayTime_eq_of_coordinates (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (s t : DiskRayTime)
    (hangle : (diskRayAngle γ hi he s : UnitAddCircle) = diskRayAngle γ hi he t)
    (hdepth : diskRayDepth γ s = diskRayDepth γ t) : s = t := by
  apply Subtype.ext
  apply hi
  apply Complex.ext_norm_arg
  · have hd : Real.log ‖γ s.val‖ = Real.log ‖γ t.val‖ := neg_injective hdepth
    have hexp := congrArg Real.exp hd
    simpa only [Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he s)),
      Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he t))] using hexp
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    exact (diskRayAngle_projects γ hi he s).symm.trans
      (hangle.trans (diskRayAngle_projects γ hi he t))

def translatedDiskRay (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (k : ℤ) : C(DiskRayTime, ℝ × ℝ) :=
  ⟨fun t => (diskRayAngle γ hi he t + (k : ℝ), diskRayDepth γ t),
    ((continuous_diskRayAngle γ hi he).add continuous_const).prodMk
      (continuous_diskRayDepth γ hi he)⟩

theorem translatedDiskRay_eq_iff (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (k l : ℤ) (s t : DiskRayTime) :
    translatedDiskRay γ hi he k s = translatedDiskRay γ hi he l t ↔ k = l ∧ s = t := by
  constructor
  · intro h
    have ha : diskRayAngle γ hi he s + (k : ℝ) = diskRayAngle γ hi he t + (l : ℝ) :=
      congrArg Prod.fst h
    have hd : diskRayDepth γ s = diskRayDepth γ t := congrArg Prod.snd h
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    have hl : ((l : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (l : ℝ) 0).mpr ⟨l, by simp⟩
    have hs : s = t := diskRayTime_eq_of_coordinates γ hi he s t (by
      have hc := congrArg (fun x : ℝ => (x : UnitAddCircle)) ha
      simpa only [AddCircle.coe_add, hk, hl, add_zero] using hc) hd
    subst t
    exact ⟨Int.cast_injective (add_left_cancel ha), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pairwise_disjoint_translatedDiskRays (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) :
    Pairwise (Disjoint on fun k : ℤ => range (translatedDiskRay γ hi he k)) := by
  intro k l hkl
  apply disjoint_left.mpr
  rintro x ⟨s, rfl⟩ ⟨t, ht⟩
  exact hkl ((translatedDiskRay_eq_iff γ hi he l k t s).mp ht).1.symm

end CircleDomainRigidity

end

end OAI
