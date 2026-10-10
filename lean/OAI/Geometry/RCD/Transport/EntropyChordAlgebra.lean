import OAI.Analysis.RCDHeat.CompressionIntegral
import OAI.Geometry.RCD.Transport.BranchEntropyDeficit

namespace OAI

/-! # Three actual entropy chords force a quantitative branch deficit -/

namespace RegularPointCoordinates

def EntropyChord (E : Time → ℝ) (A : ℝ) : Prop :=
  ∀ s t r : Time, E (timeSegment s t r) ≤
    (1-(r:ℝ))*E s+(r:ℝ)*E t+A*(r:ℝ)*(1-(r:ℝ))*|(s:ℝ)-(t:ℝ)|^2

theorem entropy_chord_cleared {E : Time → ℝ} {A : ℝ} (h : EntropyChord E A)
    (s u t : Time) (hsu : s ≤ u) (hut : u ≤ t) (hst : s < t) :
    ((t:ℝ)-(s:ℝ))*E u ≤ ((t:ℝ)-(u:ℝ))*E s+((u:ℝ)-(s:ℝ))*E t+
      A*((u:ℝ)-(s:ℝ))*((t:ℝ)-(u:ℝ))*((t:ℝ)-(s:ℝ)) := by
  have hd : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  let r : Time := ⟨((u:ℝ)-(s:ℝ))/((t:ℝ)-(s:ℝ)),
    div_nonneg (sub_nonneg.mpr hsu) hd.le,(div_le_one hd).mpr (sub_le_sub_right (show (u:ℝ) ≤ (t:ℝ) from hut) _)⟩
  have he : timeSegment s t r=u := by
    apply Subtype.ext
    change (1-(((u:ℝ)-(s:ℝ))/((t:ℝ)-(s:ℝ))))*(s:ℝ)+
      (((u:ℝ)-(s:ℝ))/((t:ℝ)-(s:ℝ)))*(t:ℝ)=(u:ℝ)
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_left (h s t r) hd.le
  rw [he] at hh
  convert hh using 1
  dsimp only [r]
  rw [sq_abs]
  field_simp
  ring

theorem entropy_chord_branch_deficit {E₀ E₁ Em : Time → ℝ} {A M B L : ℝ}
    (h₀ : EntropyChord E₀ A) (h₁ : EntropyChord E₁ A) (hm : EntropyChord Em A)
    (s t : Time) (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (hc₀ : E₀ s=Em s) (hc₁ : E₁ s=Em s)
    (hsep : Em t=(E₀ t+E₁ t)/2-L)
    (hM₀ : E₀ 1 ≤ M) (hM₁ : E₁ 1 ≤ M) (hMm : Em 0 ≤ M) (hB : B ≤ Em s) :
    (s:ℝ)*(1-(s:ℝ))*L ≤
      ((t:ℝ)-(s:ℝ))*(M-B+A*(s:ℝ)*(1-(s:ℝ))) := by
  have ha := entropy_chord_cleared hm 0 s t s.property.1 hst.le (lt_trans hs hst)
  have hb := entropy_chord_cleared h₀ s t 1 hst.le t.property.2 (lt_trans hst ht)
  have hc := entropy_chord_cleared h₁ s t 1 hst.le t.property.2 (lt_trans hst ht)
  simp only [show ((0:Time):ℝ)=0 from rfl,show ((1:Time):ℝ)=1 from rfl,
    sub_zero] at ha hb hc
  rw [hc₀] at hb
  rw [hc₁] at hc
  apply branch_entropy_deficit_of_lower_bound s.property.1 s.property.2
    (sub_nonneg.mpr hst.le) hB hsep
  · have hz := mul_le_mul_of_nonneg_left hMm (sub_nonneg.mpr hst.le)
    nlinarith only [ha,hz]
  · have hz := mul_le_mul_of_nonneg_left hM₀ (sub_nonneg.mpr hst.le)
    nlinarith only [hb,hz]
  · have hz := mul_le_mul_of_nonneg_left hM₁ (sub_nonneg.mpr hst.le)
    nlinarith only [hc,hz]

end RegularPointCoordinates

end OAI
