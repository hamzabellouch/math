import OAI.Probability.SLE.Geometry.InvertedExterior
import OAI.Probability.SLE.Geometry.ReflectedSimpleArc

namespace OAI

/-! The two sides of an inverted reflected slit run to infinity.
Consequently its complementary components cannot be bounded. -/
noncomputable section
open Set Complex Metric Filter Function
open scoped Topology ComplexConjugate

namespace SLEExactGauge

def invertedArcImage (p : C(unitInterval,ℂ)) : Set ℂ :=
  (fun t => (p t)⁻¹) '' Ioi (0:unitInterval)

lemma invertedArcImage_preconnected (p : C(unitInterval,ℂ))
    (hn : ∀ t : unitInterval, 0 < t → p t ≠ 0) :
    IsPreconnected (invertedArcImage p) := by
  apply isPreconnected_Ioi.image
  intro t ht
  exact (p.continuous.continuousAt.inv₀ (hn t ht)).continuousWithinAt

lemma invertedArcImage_unbounded (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hn : ∀ t : unitInterval, 0 < t → p t ≠ 0) :
    ¬ Bornology.IsBounded (invertedArcImage p) := by
  intro hb
  obtain ⟨R,hR,hbound⟩ := hb.subset_ball_lt 0 (0:ℂ)
  have : NeBot (𝓝[>] (0:unitInterval)) :=
    nhdsWithin_Ioi_neBot' ⟨1,by norm_num⟩ le_rfl
  have hlim : Tendsto p (𝓝[>] (0:unitInterval)) (𝓝 (0:ℂ)) := by
    simpa only [h0] using (p.continuous.tendsto (0:unitInterval)).mono_left nhdsWithin_le_nhds
  have hnear := hlim.eventually (ball_mem_nhds (0:ℂ) (by positivity : 0 < 1/(R+1)))
  have hpos : ∀ᶠ t : unitInterval in 𝓝[>] (0:unitInterval), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hsmall⟩ := (hpos.and hnear).exists
  have hnpt : 0 < ‖p t‖ := norm_pos_iff.mpr (hn t ht)
  have hsize : ‖p t‖ < 1/(R+1) := by
    simpa only [mem_ball,dist_zero_right] using hsmall
  have hbig : R+1 < ‖p t‖⁻¹ := by
    rw [← one_div,lt_div_iff₀ hnpt]
    nlinarith [(lt_div_iff₀ (by linarith : 0 < R+1)).mp hsize]
  have hless : ‖p t‖⁻¹ < R := by
    simpa only [mem_ball,dist_zero_right,norm_inv] using hbound ⟨t,ht,rfl⟩
  linarith

lemma invertedExterior_two_arcs_complement
    (p q : C(unitInterval,ℂ)) (hp0 : p 0=0) (hq0 : q 0=0)
    (hp : ∀ t : unitInterval, 0 < t → p t ≠ 0)
    (hq : ∀ t : unitInterval, 0 < t → q t ≠ 0) :
    (invertedExterior (range p ∪ range q))ᶜ = invertedArcImage p ∪ invertedArcImage q := by
  have himage (r : C(unitInterval,ℂ)) (hr0 : r 0=0) (z : ℂ) (hz : z ≠ 0) :
      z⁻¹ ∈ range r ↔ z ∈ invertedArcImage r := by
    constructor
    · rintro ⟨t,ht⟩
      have ht0 : t ≠ 0 := by intro h; rw [h,hr0] at ht; exact (inv_ne_zero hz) ht.symm
      exact ⟨t,pos_iff_ne_zero.mpr ht0,by change (r t)⁻¹=z; rw [ht,inv_inv]⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,by rw [inv_inv]⟩
  ext z
  by_cases hz : z=0
  · subst z
    have hn (r : C(unitInterval,ℂ)) (hr : ∀ t : unitInterval, 0 < t → r t ≠ 0) :
        (0:ℂ) ∉ invertedArcImage r := by
      rintro ⟨t,ht,he⟩
      exact inv_ne_zero (hr t ht) he
    simp only [mem_compl_iff,zero_mem_invertedExterior,not_true_eq_false,
      mem_union,hn p hp,hn q hq,false_or]
  · change (¬ (z=0 ∨ z⁻¹ ∉ range p ∪ range q)) ↔
      z ∈ invertedArcImage p ∪ invertedArcImage q
    simp only [hz,false_or,not_not,mem_union,himage p hp0 z hz,himage q hq0 z hz]

theorem invertedExterior_two_arcs_components_unbounded
    (p q : C(unitInterval,ℂ)) (hp0 : p 0=0) (hq0 : q 0=0)
    (hp : ∀ t : unitInterval, 0 < t → p t ≠ 0)
    (hq : ∀ t : unitInterval, 0 < t → q t ≠ 0)
    {z : ℂ} (hz : z ∉ invertedExterior (range p ∪ range q)) :
    ¬ Bornology.IsBounded
      (connectedComponentIn (invertedExterior (range p ∪ range q))ᶜ z) := by
  change z ∈ (invertedExterior (range p ∪ range q))ᶜ at hz
  rw [invertedExterior_two_arcs_complement p q hp0 hq0 hp hq] at hz ⊢
  rcases hz with hz|hz
  · have hsub := (invertedArcImage_preconnected p hp).subset_connectedComponentIn hz
      (subset_union_left : invertedArcImage p ⊆ invertedArcImage p ∪ invertedArcImage q)
    exact fun hb => invertedArcImage_unbounded p hp0 hp (hb.subset hsub)
  · have hsub := (invertedArcImage_preconnected q hq).subset_connectedComponentIn hz
      (subset_union_right : invertedArcImage q ⊆ invertedArcImage p ∪ invertedArcImage q)
    exact fun hb => invertedArcImage_unbounded q hq0 hq (hb.subset hsub)

end SLEExactGauge

end

end OAI
