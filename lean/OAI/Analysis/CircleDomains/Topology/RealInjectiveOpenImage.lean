import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! The one-dimensional open-image fact needed to recognize a Jordan
boundary inside a regular scalar level. Only interval monotonicity and
the intermediate value theorem are used. -/
open Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma real_injective_interval_image_mem_nhds {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b)) :
    f '' Ioo a b ∈ 𝓝 (f x) := by
  obtain ⟨u, hau, hux⟩ := exists_between hx.1
  obtain ⟨v, hxv, hvb⟩ := exists_between hx.2
  have hu : u ∈ Ioo a b := ⟨hau, hux.trans hx.2⟩
  have hv : v ∈ Ioo a b := ⟨hx.1.trans hxv, hvb⟩
  rcases hf.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hi with hm | hm
  · have hux' := hm hu hx hux
    have hxv' := hm hx hv hxv
    apply mem_of_superset (Ioo_mem_nhds hux' hxv')
    exact fun y hy => isPreconnected_Ioo.intermediate_value hu hv hf ⟨hy.1.le, hy.2.le⟩
  · have hvx' := hm hx hv hxv
    have hxu' := hm hu hx hux
    apply mem_of_superset (Ioo_mem_nhds hvx' hxu')
    exact fun y hy => isPreconnected_Ioo.intermediate_value hv hu hf ⟨hy.1.le, hy.2.le⟩

lemma real_open_image_of_continuousOn_injOn {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hi : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
  exact mem_of_superset (real_injective_interval_image_mem_nhds ⟨hax, hxb⟩
    (hf.mono hab) (hi.mono hab)) (image_mono hab)

end CircleDomainRigidity

end

end OAI
