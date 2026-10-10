import OAI.Geometry.NodalSets.Elliptic.SignEventMarkov
import OAI.Geometry.NodalSets.Elliptic.StrictSignSubballs

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set
open scoped ContDiff ENNReal
noncomputable section

lemma positive_real_probability_floor {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ENNReal.ofReal q ≤ p := by
  let b := min p 1
  have hb : 0 < b := lt_min hp (by norm_num)
  have ht : b ≠ ⊤ := ne_of_lt ((min_le_right p 1).trans_lt (by norm_num))
  refine ⟨b.toReal,ENNReal.toReal_pos hb.ne' ht,?_,?_⟩
  · have hh := ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (min_le_right p 1)
    simpa using hh
  · rw [ENNReal.ofReal_toReal ht]
    exact min_le_left p 1

lemma sign_subball_constants {tau p C : ℝ} (ht : 0 < tau) (ht1 : tau < 1)
    (hp : 0 < p) (hC : 0 ≤ C) :
    ∃ L > 0, ∃ r > 0, r < tau/4 ∧ r < (1-tau)/2 ∧ 4*L*r < 1 ∧ 2*C ≤ p*L := by
  let L := 2*C/p+1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨r,hr,hrt,hr1,hrL⟩ := choose_sign_subball_radius ht ht1 hL.le
  refine ⟨L,hL,r,hr,hrt,hr1,hrL,?_⟩
  dsimp [L]
  have he : p*(2*C/p+1) = 2*C+p := by field_simp
  rw [he]
  linarith

lemma sign_subballs_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → Coord → ℝ)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (G : Ω → ℝ)
    (hG : Integrable G μ) (hG0 : ∀ a, 0 ≤ G a)
    {tau r p C L : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (hL : 0 < L)
    (htr : tau+r ≤ 1) (hsmall : 4*L*r < 1) (hmean : (∫ a, G a ∂μ) ≤ C)
    (hCL : 2*C ≤ p*L)
    (hgrad : ∀ a, G a ≤ L → ∀ x : Coord, sourceEuclideanNorm x ≤ 1 →
      sourceEuclideanNorm (fun i ↦ fderiv ℝ (F a) x (Pi.single i 1)) ≤ L)
    (j : Fin 4) (hsign : p ≤ μ.real {a | 1 ≤ F a 0 ∧ F a (tau • Pi.single j 1) ≤ -1}) :
    p/2 ≤ μ.real {a |
      (∀ v : Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1 ∧ 0 < F a v) ∧
      (∀ v : Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
        sourceEuclideanNorm v ≤ 1 ∧ F a v < 0)} := by
  have hh := event_inter_gradient_half hG hG0 hL hsign (by linarith : 2*(∫ a, G a ∂μ) ≤ p*L)
  apply hh.trans
  apply measureReal_mono
  · intro a ha
    exact strict_sign_subballs (F a) (hF a) ht hr hL.le htr hsmall j ha.1.1 ha.1.2
      (hgrad a ha.2)
  · exact measure_ne_top _ _

end
end Yau.Geometry

end OAI
