import OAI.Probability.SLE.Gauge.RibbonGoodPrefix

namespace OAI

/-! Recover the actual continuous ribbon coordinates at a successful
first front without adding any chart distortion assumptions. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage

theorem goodRibbonPrefix_coordinates
    (γ : ℝ≥0 → ℂ) (hc : Continuous γ) (P : ℂ → ℂ)
    (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (hi : InjOn P closedRibbon) (g : C(ℂ, ℝ))
    (hg : ∀ z ∈ closedRibbon, g (P z) = z.re) (hg0 : g (γ 0) = 0)
    {k ε : ℝ} (hk : 0 < k)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ)
      (fun _ => firstFrontTime (fun t => g (γ t)) k) P ε) :
    ∃ (T : ℝ≥0) (x : ℝ) (xp : ℝ≥0 → ℂ),
      firstFrontTime (fun t => g (γ t)) k = (T : WithTop ℝ≥0) ∧ 0 < T ∧ |x| ≤ ε / 4 ∧
      ContinuousOn xp (Icc 0 T) ∧ EqOn γ (P ∘ xp) (Icc 0 T) ∧
      (xp 0).re = 0 ∧ xp T = (k : ℂ) + (x : ℂ) * Complex.I ∧
      MapsTo xp (Icc 0 T) closedRibbon ∧
      (∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε) ∧
      ∀ t : ℝ≥0, t < T → (xp t).re < k := by
  cases hτ : firstFrontTime (fun t => g (γ t)) k with
  | top => exact False.elim (hpref.1 hτ)
  | coe T =>
    have hpast : MapsTo γ (Icc 0 T) (ribbonCore P ε) := by
      simpa only [hτ, WithTop.untopD_coe] using hpref.2.1
    have hend : γ T ∈ ribbonCore P (ε / 4) := by
      simpa only [hτ, WithTop.untopD_coe] using hpref.2.2
    let xp := fun t => coordinateInverse P closedRibbon (γ t)
    have hmap : MapsTo γ (Icc 0 T) (P '' closedRibbon) :=
      fun _ ht => image_mono inter_subset_left (hpast ht)
    have hcoords : MapsTo xp (Icc 0 T) closedRibbon := fun _ ht => coordinateInverse_mem (hmap ht)
    have hxpc : ContinuousOn xp (Icc 0 T) :=
      (coordinateInverse_continuousOn_of_embedding P hemb.isEmbedding).comp hc.continuousOn hmap
    have hγeq : EqOn γ (P ∘ xp) (Icc 0 T) := fun _ ht => (coordinateInverse_right (hmap ht)).symm
    have hgt (t : ℝ≥0) (ht : t ∈ Icc 0 T) : g (γ t) = (xp t).re := by
      rw [hγeq ht]
      exact hg _ (hcoords ht)
    have hhit : g (γ T) = k := FrontSuccessMeasurability.firstFrontTime_attained _ (g.continuous.comp hc) k T hτ
    have hT : 0 < T := by
      apply lt_of_le_of_ne bot_le
      intro he
      rw [← he] at hhit
      change g (γ 0) = k at hhit
      rw [hg0] at hhit
      exact hk.ne' hhit.symm
    have hxre : (xp T).re = k := (hgt T ⟨bot_le, le_rfl⟩).symm.trans hhit
    have htip : xp T = (k : ℂ) + ((xp T).im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hxre]
    have hx : |(xp T).im| ≤ ε / 4 := by
      obtain ⟨z, ⟨hz, hiε⟩, he⟩ := hend
      simpa only [xp, ← he, coordinateInverse_left hi hz] using hiε
    have hstrict : ∀ t : ℝ≥0, t < T → (xp t).re < k := by
      have hh := strict_before_attained_front (fun t => g (γ t)) k T
        (g.continuous.comp hc).continuousOn (by rw [hg0]; exact hk) hτ
      intro t ht
      rw [← hgt t ⟨bot_le, ht.le⟩]
      exact hh t ht
    refine ⟨T, (xp T).im, xp, rfl, hT, hx, hxpc, hγeq,
      by rw [← hgt 0 ⟨bot_le, bot_le⟩, hg0], htip, hcoords, ?_, hstrict⟩
    intro t ht
    refine ⟨?_, ?_⟩
    · rcases ht.2.eq_or_lt with rfl | hlt
      · exact hxre.le
      · exact (hstrict t hlt).le
    · obtain ⟨z, ⟨hz, hiε⟩, he⟩ := hpast ht
      simpa only [xp, ← he, coordinateInverse_left hi hz] using hiε

end SLEExactGauge

end

end OAI
