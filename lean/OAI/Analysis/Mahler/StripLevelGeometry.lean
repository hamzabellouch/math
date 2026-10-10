import OAI.Analysis.Mahler.StripMassExhaustion
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! Positive levels of the literal strip tau are the compact boundaries of its
strict sublevels. This supplies set geometry, not boundary-chart integration. -/
noncomputable section
namespace SymmetricMahler
open Set Filter
open scoped Topology
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The actual level set is compact in the ambient real 2n-space. -/
theorem isCompact_strip_level (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    IsCompact {z | z ∈ stripDomain A ∧ stripTau A m z = R} := by
  have hK := isCompact_strip_closed_sublevel A hA hm hR hR1
  have hKU : {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} ⊆ stripDomain A :=
    fun _ hz => hz.1
  have hc := ((stripGeometry_continuousOn_tau A m).mono hKU).preimage_isClosed_of_isClosed
    hK.isClosed (isClosed_singleton (x := R))
  have he : {z | z ∈ stripDomain A ∧ stripTau A m z = R} =
      {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} ∩ (stripTau A m) ⁻¹' {R} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, ht⟩
      exact ⟨⟨hz, ht.le⟩, ht⟩
    · rintro ⟨⟨hz, _⟩, ht⟩
      exact ⟨hz, ht⟩
  rw [he]
  exact hK.of_isClosed_subset hc inter_subset_left

/-- The boundary used in Stokes is exactly tau=R, with no boundary-identification premise. -/
theorem frontier_strip_sublevel (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    frontier {z | z ∈ stripDomain A ∧ stripTau A m z < R} =
      {z | z ∈ stripDomain A ∧ stripTau A m z = R} := by
  let S := {z | z ∈ stripDomain A ∧ stripTau A m z < R}
  have hS : IsOpen S := isOpen_strip_sublevel A m R
  have hclosed := (isCompact_strip_closed_sublevel A hA hm hR.le hR1).isClosed
  have hclosure : closure S ⊆ {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} :=
    closure_minimal (fun _ hz => ⟨hz.1, hz.2.le⟩) hclosed
  change frontier S = _
  rw [frontier, hS.interior_eq]
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    have hc := hclosure hz
    exact ⟨hc.1, le_antisymm hc.2 (le_of_not_gt (fun ht => hn ⟨hc.1, ht⟩))⟩
  · rintro ⟨hz, ht⟩
    refine ⟨?_, fun hs => (ne_of_lt hs.2) ht⟩
    by_contra hn
    have hmin : IsLocalMin (stripTau A m) z := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn,
        (stripGeometry_isOpen_domain A).mem_nhds hz] with w hw hwu
      rw [ht]
      exact le_of_not_gt (fun hwlt => hw (subset_closure (show w ∈ S from ⟨hwu, hwlt⟩)))
    have he := hmin.fderiv_eq_zero
    obtain ⟨v, hv⟩ := stripTau_positive_regular A hA hm hR hz ht (1 : ℝ)
    rw [he] at hv
    norm_num at hv

end SymmetricMahler

end

end OAI
