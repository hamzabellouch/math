import OAI.Analysis.CircleDomains.Selection.RegularPiecePeriodicParametrization
import OAI.Analysis.CircleDomains.Topology.RegularJordanLevelComponent
import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization

namespace OAI

/-! A prescribed regular Jordan boundary has an actual regular periodic
parametrization. No circle-classification input is used, and the rest of
its defining scalar level is allowed to be unbounded. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_boundary_parametrization (H : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ γ : ℝ → ℂ, RegularJordanParametrization H γ := by
  let K := frontier (jordanInterior H)
  have hK : IsCompact K := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hconn : IsConnected K := isConnected_frontier_jordanInterior H
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨x,hx⟩ := hconn.nonempty
  obtain ⟨F⟩ := exists_compact_regular_piece_flow hf ht hK hlevel
    (regular_jordan_boundary_open_in_level H hf ht hlevel)
  obtain ⟨γ,hs,hp,hi,hr,himage⟩ := F.exists_regular_period_one hf ht hK ⟨x,hx⟩
  have hfull : range γ = K := by
    rw [himage,PreconnectedSpace.connectedComponent_eq_univ,image_univ,Subtype.range_val]
  refine ⟨γ,hs,hp,hi,hr,?_⟩
  apply Subset.antisymm
  · exact (image_subset_range _ _).trans hfull.subset
  · intro z hz
    have hzr : z ∈ range γ := hfull.symm ▸ (show z ∈ K from hz)
    obtain ⟨s,hsz⟩ := hzr
    refine ⟨Int.fract s,⟨Int.fract_nonneg s,(Int.fract_lt_one s).le⟩,?_⟩
    have he : γ (Int.fract s) = γ s := by
      simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq (x := s) ⌊s⌋
    exact he.trans hsz

end CircleDomainRigidity

end

end OAI
