import OAI.Geometry.IsometricImmersion.Curvature.NegativeCurvatureHeight
import Mathlib.Topology.Order.Compact

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem exists_localExtr_of_constant_frontier
    {S : Set Coord} {z : Coord → ℝ} (hS : IsCompact S)
    (hne : (interior S).Nonempty) (hz : ContinuousOn z S)
    (c : ℝ) (hfront : ∀ p ∈ frontier S, z p = c) :
    ∃ p ∈ interior S, IsLocalExtr z p := by
  obtain ⟨p, hp⟩ := hne
  have hSn : S.Nonempty := ⟨p, interior_subset hp⟩
  obtain ⟨a, ha, hmax⟩ := hS.exists_isMaxOn hSn hz
  obtain ⟨b, hb, hmin⟩ := hS.exists_isMinOn hSn hz
  by_cases hai : a ∈ interior S
  · exact ⟨a, hai, Or.inr (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hai))⟩
  by_cases hbi : b ∈ interior S
  · exact ⟨b, hbi, Or.inl (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hbi))⟩
  have hac : z a = c := hfront a ⟨subset_closure ha, hai⟩
  have hbc : z b = c := hfront b ⟨subset_closure hb, hbi⟩
  have hzconst : ∀ q ∈ S, z q = c := by
    intro q hq
    exact le_antisymm (hac ▸ hmax hq) (hbc ▸ hmin hq)
  have hmaxp : IsMaxOn z S p := by
    intro q hq
    change z q ≤ z p
    rw [hzconst q hq, hzconst p (interior_subset hp)]
  exact ⟨p, hp, Or.inr (hmaxp.isLocalMax (mem_interior_iff_mem_nhds.mp hp))⟩

theorem immersion_height_not_constant_frontier
    {g : MetricField} {F : Coord → Ambient} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) (hne : (interior S).Nonempty)
    (hK : ∀ p ∈ interior S, gaussianCurvature g p < 0)
    (e : Ambient) (he : inner ℝ e e = 1) :
    ¬∃ c : ℝ, ∀ p ∈ frontier S, height F e p = c := by
  rintro ⟨c, hc⟩
  obtain ⟨p, hp, hextr⟩ := exists_localExtr_of_constant_frontier hS hne
    ((height_smooth hF.1 e).continuousOn.mono hSU) c hc
  exact immersion_height_no_localExtr hg hF hU e he (hSU (interior_subset hp))
    (hK p hp) hextr

end SmoothLocal.Geometry

end

end OAI
