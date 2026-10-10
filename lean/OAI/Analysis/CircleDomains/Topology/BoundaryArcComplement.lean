import OAI.Analysis.CircleDomains.Topology.BoundaryClosingArc

namespace OAI

/-! The unused part of the unit circle after closing a crosscut is one
connected open arc, with its exact angular parameter interval. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma boundaryClosingArc_complement_image {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    (fun s : ℝ => standardCirclePoint (s : UnitAddCircle)) ''
        Ioo (unitCircleCut (normalizedArgument a)) 1 =
      Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  let α := unitCircleCut (normalizedArgument a)
  have hα : 0 < α := boundary_angle_pos ha ha1
  have hα1 : α < 1 := (unitCircleCut_mem _).2
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨mem_sphere_zero_iff_norm.mpr (Circle.norm_coe _), ?_⟩
    rintro ⟨t, ht⟩
    have he := standardCirclePoint_injective ht
    change ((α*(t : ℝ) : ℝ) : UnitAddCircle) = (s : UnitAddCircle) at he
    have ht' : α * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 t
    have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := by
      exact ⟨(hα.trans hs.1).le, by simpa using hs.2⟩
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' hs').mp he
    have htle : α*(t : ℝ) ≤ α := mul_le_of_le_one_right hα.le t.property.2
    exact (not_lt_of_ge (he' ▸ htle)) hs.1
  · rintro ⟨hz, hznot⟩
    let s := unitCircleCut (normalizedArgument z)
    have hs : s ∈ Ico (0 : ℝ) 1 := unitCircleCut_mem _
    have he : standardCirclePoint (s : UnitAddCircle) = z := by
      rw [show (s : UnitAddCircle) = normalizedArgument z from AddCircle.coe_equivIco]
      exact standardCirclePoint_normalizedArgument (mem_sphere_zero_iff_norm.mp hz)
    have hsα : α < s := by
      by_contra! hh
      let t : PathTime := ⟨s/α, ⟨div_nonneg hs.1 hα.le, (div_le_one hα).mpr hh⟩⟩
      apply hznot
      refine ⟨t, ?_⟩
      change standardCirclePoint ((α*(s/α) : ℝ) : UnitAddCircle) = z
      rw [mul_div_cancel₀ s hα.ne']
      exact he
    exact ⟨s, ⟨hsα,hs.2⟩,he⟩

lemma isConnected_boundaryClosingArc_complement {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    IsConnected (Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha)) := by
  rw [← boundaryClosingArc_complement_image ha ha1]
  apply (isConnected_Ioo ((unitCircleCut_mem (normalizedArgument a)).2)).image
  exact ((continuous_subtype_val.comp
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn

end CircleDomainRigidity

end

end OAI
