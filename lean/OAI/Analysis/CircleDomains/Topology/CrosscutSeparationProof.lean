import OAI.Analysis.CircleDomains.Topology.DiskCrosscutSides

namespace OAI

/-! Disk crosscut separation derived from the retained planar Schoenflies input. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem unitDiskCrosscutSeparation (hsch : PlanarSchoenflies) :
    UnitDiskCrosscutSeparation := by
  intro p hi ha hb hp
  have hb0 : p 1 ≠ 0 := by
    intro h
    rw [h,norm_zero] at hb
    exact zero_ne_one hb
  let R := Homeomorph.mulLeft₀ (p 1) hb0
  let q : Path ((p 1)⁻¹ * p 0) 1 := {
    toFun := fun t => (p 1)⁻¹ * p t
    continuous_toFun := continuous_const.mul p.continuous
    source' := rfl
    target' := inv_mul_cancel₀ hb0 }
  have hqp (t : PathTime) : R (q t) = p t := by
    change p 1 * ((p 1)⁻¹ * p t) = p t
    rw [← mul_assoc,mul_inv_cancel₀ hb0,one_mul]
  have hqnorm (t : PathTime) : ‖q t‖ = ‖p t‖ := by
    change ‖(p 1)⁻¹ * p t‖ = ‖p t‖
    rw [norm_mul,norm_inv,hb,inv_one,one_mul]
  have hqa : ‖(p 1)⁻¹ * p 0‖ = 1 := (hqnorm 0).trans ha
  have hqa1 : (p 1)⁻¹ * p 0 ≠ 1 := by
    intro h
    have he : p 0 = p 1 := by
      rw [← hqp 0]
      change p 1 * ((p 1)⁻¹ * p 0) = p 1
      rw [h,mul_one]
    have hh : (0 : PathTime) = 1 := hi he
    exact zero_ne_one (congrArg (fun t : PathTime => (t : ℝ)) hh)
  have hqi : Injective q := fun s t he => hi (by rw [← hqp s,← hqp t,he])
  have hqpint : ∀ t ∈ Ioo (0 : PathTime) 1, ‖q t‖ < 1 := by
    intro t ht
    rw [hqnorm]
    exact hp t ht
  obtain ⟨U,V,hU,hV,hUc,hVc,hd,hu,hfu,hfv⟩ :=
    disk_crosscut_sides_at_one hsch q hqi hqpint hqa hqa1
  have hRnorm (z : ℂ) : ‖R z‖ = ‖z‖ := by
    change ‖p 1 * z‖ = ‖z‖
    rw [norm_mul,hb,one_mul]
  have hRb : R '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa only [mem_ball_zero_iff,hRnorm] using hw
    · intro hz
      refine ⟨R.symm z,?_,R.apply_symm_apply z⟩
      rw [mem_ball_zero_iff,← hRnorm, R.apply_symm_apply]
      exact mem_ball_zero_iff.mp hz
  have hRrange : R '' range q = range p := by
    rw [← range_comp]
    exact congrArg range (funext hqp)
  refine ⟨R '' U,R '' V,R.isOpenMap U hU,R.isOpenMap V hV,
    hUc.image R R.continuous.continuousOn,hVc.image R R.continuous.continuousOn,
    ?_,?_,?_,?_⟩
  · rw [disjoint_iff_inter_eq_empty,← image_inter R.injective,hd.inter_eq,image_empty]
  · rw [← image_union,hu,image_sdiff R.injective,hRb,hRrange]
  · rw [← R.image_frontier,← hRb,← image_inter R.injective,hfu,
      image_inter R.injective,hRrange,hRb]
  · rw [← R.image_frontier,← hRb,← image_inter R.injective,hfv,
      image_inter R.injective,hRrange,hRb]

end CircleDomainRigidity

end

end OAI
