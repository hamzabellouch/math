import OAI.Probability.SLE.Loewner.TargetJointMeasurability

namespace OAI

/-! Joint angle, level and driver measurability of the exact rational
level stop and its prescribed change-of-law density. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma levelTime_eq_iInf (κ θ : ℝ) (b : Driver) (ℓ : ℝ) :
    levelTime κ θ b ℓ = ⨅ q : ℚ,
      if 0 < q ∧ Surviving κ b (diskMapInv θ 0) q ∧ ℓ < clock κ θ b 0 q
      then ENNReal.ofReal (q : ℝ) else ∞ := by
  apply le_antisymm
  · apply le_iInf
    intro q
    split_ifs with hq
    · exact sInf_le ⟨q,hq.1,rfl,hq.2.1,hq.2.2⟩
    · exact le_top
  · apply le_sInf
    rintro t ⟨q,hq,rfl,hs,hc⟩
    exact iInf_le_of_le q (by simp only [hq,hs,hc,and_self,ite_true,le_refl])

lemma measurable_levelTime_joint (κ : ℝ) :
    Measurable (fun p : ℝ × (ℝ × Driver) => levelTime κ p.2.1 p.2.2 p.1) := by
  have he : (fun p : ℝ × (ℝ × Driver) => levelTime κ p.2.1 p.2.2 p.1) =
      (fun p => ⨅ q : ℚ,
        if 0 < q ∧ Surviving κ p.2.2 (diskMapInv p.2.1 0) q ∧
          p.1 < clock κ p.2.1 p.2.2 0 q
        then ENNReal.ofReal (q : ℝ) else ∞) :=
    funext (fun p => levelTime_eq_iInf κ p.2.1 p.2.2 p.1)
  rw [he]
  apply Measurable.iInf
  intro q
  by_cases hq : (0:ℚ) < q
  · let t : ℝ≥0 := NNReal.mk (q:ℝ) (Rat.cast_nonneg.mpr hq.le)
    have hp : Measurable (fun p : ℝ × (ℝ × Driver) =>
        (t,(p.2.1,(p.2.2,(0:ℂ))))) :=
      measurable_const.prodMk (measurable_snd.fst.prodMk
        (measurable_snd.snd.prodMk measurable_const))
    have hs : MeasurableSet {p : ℝ × (ℝ × Driver) |
        Surviving κ p.2.2 (diskMapInv p.2.1 0) (q:ℝ)} :=
      hp (measurableSet_disk_surviving_joint κ)
    have hc : Measurable (fun p : ℝ × (ℝ × Driver) => clock κ p.2.1 p.2.2 0 (q:ℝ)) :=
      @Measurable.comp (ℝ × (ℝ × Driver)) (ℝ≥0 × (ℝ × (Driver × ℂ))) ℝ
        inferInstance inferInstance inferInstance
        (fun p => clock κ p.2.1 p.2.2.1 p.2.2.2 p.1)
        (fun p => (t,(p.2.1,(p.2.2,(0:ℂ))))) (measurable_clock_joint κ) hp
    have hA := hs.inter (measurableSet_lt measurable_fst hc)
    simpa only [hq,true_and] using
      (measurable_const.ite hA measurable_const : Measurable
        (fun p : ℝ × (ℝ × Driver) =>
          if Surviving κ p.2.2 (diskMapInv p.2.1 0) (q:ℝ) ∧
            p.1 < clock κ p.2.1 p.2.2 0 (q:ℝ)
          then ENNReal.ofReal (q:ℝ) else ∞))
  · simp only [hq,false_and,ite_false]
    exact measurable_const

lemma measurable_levelTime_angle (κ ℓ : ℝ) :
    Measurable (fun p : ℝ × Driver => levelTime κ p.1 p.2 ℓ) :=
  @Measurable.comp (ℝ × Driver) (ℝ × (ℝ × Driver)) ℝ≥0∞
    inferInstance inferInstance inferInstance
    (fun p => levelTime κ p.2.1 p.2.2 p.1) (fun p => (ℓ,p))
    (measurable_levelTime_joint κ) (measurable_const.prodMk measurable_id)

lemma measurable_levelDensity_joint (κ : ℝ) :
    Measurable (fun p : ℝ × (ℝ × Driver) => levelDensity κ p.2.1 p.2.2 p.1) := by
  have hτ := measurable_levelTime_joint κ
  have ht : Measurable (fun p : ℝ × (ℝ × Driver) =>
      (levelTime κ p.2.1 p.2.2 p.1).toReal.toNNReal) :=
    continuous_real_toNNReal.measurable.comp hτ.ennreal_toReal
  have hp : Measurable (fun p : ℝ × (ℝ × Driver) =>
      ((levelTime κ p.2.1 p.2.2 p.1).toReal.toNNReal,
        (p.2.1,(p.2.2,(0:ℂ))))) :=
    ht.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_const))
  have ha : Measurable (fun p : ℝ × (ℝ × Driver) =>
      angle κ p.2.1 p.2.2 0 (levelTime κ p.2.1 p.2.2 p.1).toReal) := by
    have hm := @Measurable.comp (ℝ × (ℝ × Driver)) (ℝ≥0 × (ℝ × (Driver × ℂ))) ℝ
      inferInstance inferInstance inferInstance
      (fun p => angle κ p.2.1 p.2.2.1 p.2.2.2 p.1)
      (fun p => ((levelTime κ p.2.1 p.2.2 p.1).toReal.toNNReal,
        (p.2.1,(p.2.2,(0:ℂ))))) (measurable_angle_joint κ) hp
    simpa only [Function.comp_def,Real.toNNReal_of_nonneg ENNReal.toReal_nonneg,NNReal.coe_mk] using hm
  have hb : Measurable (fun p : ℝ × (ℝ × Driver) =>
      Real.exp (2*a κ*α κ*p.1)*
        Real.sin (angle κ p.2.1 p.2.2 0 (levelTime κ p.2.1 p.2.2 p.1).toReal)^(SLEExactGauge.Target.p κ) /
          Real.sin p.2.1^(SLEExactGauge.Target.p κ)) :=
    ((measurable_const.mul measurable_fst).exp.mul (ha.sin.pow_const (SLEExactGauge.Target.p κ))).div
      (measurable_snd.fst.sin.pow_const (SLEExactGauge.Target.p κ))
  exact hb.ite (measurableSet_lt hτ measurable_const) measurable_const

lemma measurable_levelDensity_angle (κ ℓ : ℝ) :
    Measurable (fun p : ℝ × Driver => levelDensity κ p.1 p.2 ℓ) :=
  @Measurable.comp (ℝ × Driver) (ℝ × (ℝ × Driver)) ℝ
    inferInstance inferInstance inferInstance
    (fun p => levelDensity κ p.2.1 p.2.2 p.1) (fun p => (ℓ,p))
    (measurable_levelDensity_joint κ) (measurable_const.prodMk measurable_id)

end SLEExactGauge.Target

end

end OAI
