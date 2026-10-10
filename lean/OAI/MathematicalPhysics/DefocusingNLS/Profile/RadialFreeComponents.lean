import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeInitialExistence

namespace OAI

/-! Scalar integral equations for the actual complex free profile. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialFreeField_continuousOn_curve (b l u : ℝ) (hl : 0 < l)
    (X : ℝ → ℂ × ℂ) (hX : Continuous X) :
    ContinuousOn (fun t => radialFreeField b t (X t)) (Icc l u) := by
  have hdiv : ContinuousOn (fun t : ℝ => 11/t) (Icc l u) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hl.trans_le ht.1))
  have hc : ContinuousOn radialFreeCoefficient (Icc l u) :=
    (Complex.continuous_ofReal.comp_continuousOn hdiv).add
      (continuousOn_const.mul ((Complex.continuous_ofReal.comp (continuous_id.div_const 2)).continuousOn))
  exact hX.snd.continuousOn.prodMk
    ((hc.neg.mul hX.snd.continuousOn).sub (continuousOn_const.mul hX.fst.continuousOn))

theorem exists_radial_free_components (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ)) :
    ∃ F G : ℝ → ℂ, Continuous F ∧ Continuous G ∧
      (∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t) ∧
      (∀ r ∈ Icc l u, G r=∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t) ∧
      (∀ r, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) := by
  obtain ⟨X,hX,_,he,hB⟩ := exists_radial_free_initial b l u hb hl hu hlu hwidth
  have hfi (r : ℝ) (hr : r ∈ Icc l u) :
      IntervalIntegrable (fun t => radialFreeField b t (X t)) volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((radialFreeField_continuousOn_curve b l u (by linarith) X hX).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  refine ⟨fun r => (X r).1,fun r => (X r).2,hX.fst,hX.snd,?_,?_,?_⟩
  · intro r hr
    have hf := congrArg Prod.fst (he r hr)
    have hi := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm (hfi r hr)
    change (∫ t in l..r, (X t).2)=(∫ t in l..r, radialFreeField b t (X t)).1 at hi
    change (X r).1=1+(∫ t in l..r, radialFreeField b t (X t)).1 at hf
    rwa [← hi] at hf
  · intro r hr
    have hg := congrArg Prod.snd (he r hr)
    have hi := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm (hfi r hr)
    change (∫ t in l..r, -radialFreeCoefficient t*(X t).2-(b : ℂ)*(X t).1)=
      (∫ t in l..r, radialFreeField b t (X t)).2 at hi
    change (X r).2=0+(∫ t in l..r, radialFreeField b t (X t)).2 at hg
    simpa only [← hi,zero_add] using hg
  · intro r
    exact ⟨(norm_fst_le (X r)).trans (hB r),(norm_snd_le (X r)).trans (hB r)⟩

end DefocusingNLS

end OAI
