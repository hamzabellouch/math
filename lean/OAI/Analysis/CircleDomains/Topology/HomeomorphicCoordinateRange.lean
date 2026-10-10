import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Compact

namespace OAI

/-! A coordinate of a plane homeomorphism has no interior extremum.
Its bounds on the boundary of any compact set hold throughout that set. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_im_not_local_max (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    ¬ IsLocalMax (fun w => (H w).im) z := by
  intro h
  have ho : IsOpenMap (fun w => (H w).im) :=
    (Complex.imCLM.isOpenMap Complex.im_surjective).comp H.isOpenMap
  apply (h.isLocalMaxOn univ).not_nhds_le_map
  simpa only [nhdsWithin_univ] using ho.nhds_le z

 theorem homeomorphic_im_not_local_min (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    ¬ IsLocalMin (fun w => (H w).im) z := by
  intro h
  have ho : IsOpenMap (fun w => (H w).im) :=
    (Complex.imCLM.isOpenMap Complex.im_surjective).comp H.isOpenMap
  apply (h.isLocalMinOn univ).not_nhds_le_map
  simpa only [nhdsWithin_univ] using ho.nhds_le z

 theorem homeomorphic_im_le_of_boundary (H : ℂ ≃ₜ ℂ) {K : Set ℂ} (hK : IsCompact K)
    {C : ℝ} (hbd : ∀ z ∈ frontier K, (H z).im ≤ C) :
    ∀ z ∈ K, (H z).im ≤ C := by
  intro z hz
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩
    (Complex.continuous_im.comp H.continuous).continuousOn
  have hwi : w ∉ interior K := fun hi => homeomorphic_im_not_local_max H w
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hi))
  have hwb : w ∈ frontier K := ⟨subset_closure hw, hwi⟩
  exact (hmax hz).trans (hbd w hwb)

 theorem homeomorphic_im_ge_of_boundary (H : ℂ ≃ₜ ℂ) {K : Set ℂ} (hK : IsCompact K)
    {C : ℝ} (hbd : ∀ z ∈ frontier K, C ≤ (H z).im) :
    ∀ z ∈ K, C ≤ (H z).im := by
  intro z hz
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩
    (Complex.continuous_im.comp H.continuous).continuousOn
  have hwi : w ∉ interior K := fun hi => homeomorphic_im_not_local_min H w
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hi))
  have hwb : w ∈ frontier K := ⟨subset_closure hw, hwi⟩
  exact (hbd w hwb).trans (hmin hz)

end CircleDomainRigidity

end

end OAI
