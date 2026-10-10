import OAI.Combinatorics.Crossing.CircleConnectors

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_segment (a b : Plane) (t : ℝ) :
    squaredLength (segmentPoint a b t) =
      (1-t)*squaredLength a+t*squaredLength b-t*(1-t)*squaredLength (b-a) := by
  dsimp [squaredLength,segmentPoint]
  ring

theorem unit_chord_in_disk (a b : Plane) (ha : squaredLength a=1) (hb : squaredLength b=1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : squaredLength (segmentPoint a b t) ≤ 1 := by
  have hnon : 0 ≤ squaredLength (b-a) := by dsimp [squaredLength]; positivity
  have hprod := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) hnon
  rw [squaredLength_segment,ha,hb]
  linarith

theorem unit_chord_in_open_disk (a b : Plane) (ha : squaredLength a=1) (hb : squaredLength b=1)
    (hne : a ≠ b) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : squaredLength (segmentPoint a b t) < 1 := by
  have hpos := squaredLength_pos (b-a) (sub_ne_zero.mpr hne.symm)
  have hprod := mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) hpos
  rw [squaredLength_segment,ha,hb]
  linarith

theorem unit_chord_connector_disjoint (a b u : Plane)
    (ha : squaredLength a=1) (hb : squaredLength b=1) (hu : squaredLength u=1)
    (hab : a ≠ b) (δ : ℝ) (hδ : |δ|<1) (hne : δ ≠ 0)
    (haq : a ≠ circleOffset u δ) (hbq : b ≠ circleOffset u δ) :
    ¬ ClosedSegmentsMeet a b (circleOffset u δ) (circleTangentOffset u δ) := by
  rintro ⟨s,hs,t,ht,he⟩
  by_cases htp : 0<t
  · have hinside := unit_chord_in_disk a b ha hb s hs
    have houtside := circleConnector_strictly_outside u hu δ hδ hne t htp
    have heq := congrArg squaredLength he
    linarith
  · have ht0 : t=0 := by linarith [ht.1]
    subst t
    rw [segmentPoint_zero] at he
    by_cases hs0 : s=0
    · subst s
      exact haq (by simpa using he)
    · by_cases hs1 : s=1
      · subst s
        exact hbq (by simpa using he)
      · have hs' : s ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),lt_of_le_of_ne hs.2 hs1⟩
        have hinside := unit_chord_in_open_disk a b ha hb hab s hs'
        rw [he,circleOffset_on_circle u hu δ hδ.le] at hinside
        exact (lt_irrefl _ hinside)

end Zarankiewicz

end

end OAI
