import OAI.Geometry.RCD.Transport.OrthonormalHarmonicGeodesic

namespace OAI

/-! # The interior derivative of an affine coordinate path -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem affine_path_hasDerivAt {X : Type*} [MetricSpace X] {n : ℕ}
    (γ : C(Time,X)) (v : X → Euclidean n)
    (hv : ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1))
    {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun r => v (geodesicExtension γ r)) (v (γ 1)-v (γ 0)) s := by
  have hd : HasDerivAt (fun r : ℝ => v (γ 0)+r • (v (γ 1)-v (γ 0)))
      (v (γ 1)-v (γ 0)) s := by
    simpa only [one_smul,zero_add] using!
      (hasDerivAt_const s (v (γ 0))).add ((hasDerivAt_id s).smul_const (v (γ 1)-v (γ 0)))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  have he := hv ⟨t,Ioo_subset_Icc_self ht⟩
  rw [← geodesicExtension_eq γ ⟨t,Ioo_subset_Icc_self ht⟩] at he
  change v (geodesicExtension γ t)=v (γ 0)+t • (v (γ 1)-v (γ 0))
  rw [he]
  module

end RegularPointCoordinates

end

end OAI
