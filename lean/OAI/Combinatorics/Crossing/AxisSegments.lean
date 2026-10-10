import OAI.Combinatorics.Crossing.ProperSegmentCrossing

namespace OAI

noncomputable section
namespace Zarankiewicz

def axisSegmentPoint (a b t : ℝ) : Plane := segmentPoint (0,a) (b,0) t

theorem axisSegmentPoint_coordinates (a b t : ℝ) : axisSegmentPoint a b t=(t*b,(1-t)*a) := by
  ext <;> simp [axisSegmentPoint,segmentPoint]

theorem axisSegmentPoint_injective (a b : ℝ) (hb : b ≠ 0) : Function.Injective (axisSegmentPoint a b) := by
  intro t u htu
  have hx := congrArg Prod.fst htu
  simp only [axisSegmentPoint_coordinates] at hx
  exact mul_right_cancel₀ hb hx

theorem axisSegmentPoint_interior_off_axes (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (axisSegmentPoint a b t).1 ≠ 0 ∧ (axisSegmentPoint a b t).2 ≠ 0 := by
  rw [axisSegmentPoint_coordinates]
  exact ⟨mul_ne_zero (ne_of_gt ht.1) hb,mul_ne_zero (ne_of_gt (sub_pos.mpr ht.2)) ha⟩

theorem axisSegmentPoint_same_vertical (a b d t u : ℝ) (ha : a ≠ 0)
    (ht : 0 < t) (h : axisSegmentPoint a b t=axisSegmentPoint a d u) : b=d := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have htu : t=u := by have hh := mul_right_cancel₀ ha hy; linarith
  rw [← htu] at hx
  exact mul_left_cancel₀ (ne_of_gt ht) hx

theorem axisSegmentPoint_same_horizontal (a c b t u : ℝ) (hb : b ≠ 0)
    (ht : t < 1) (h : axisSegmentPoint a b t=axisSegmentPoint c b u) : a=c := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have htu : t=u := mul_right_cancel₀ hb hx
  rw [← htu] at hy
  exact mul_left_cancel₀ (ne_of_gt (sub_pos.mpr ht)) hy

theorem axisSegmentPoint_meeting_det (a b c d t u : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) (h : axisSegmentPoint a b t=axisSegmentPoint c d u) :
    det2 ((b,0)-(0,a)) ((d,0)-(0,c)) ≠ 0 := by
  intro hz
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have hz' : a*d-b*c=0 := by
    dsimp [det2] at hz
    nlinarith [hz]
  have hac : (a-c)*b=0 := by linear_combination b*hy+a*hx+u*hz'
  have he : a=c := sub_eq_zero.mp ((mul_eq_zero.mp hac).resolve_right hb)
  have hbd : a*(d-b)=0 := by rw [← he] at hz'; nlinarith [hz']
  have he' : b=d := (sub_eq_zero.mp ((mul_eq_zero.mp hbd).resolve_left ha)).symm
  exact hne (Prod.ext he he')

theorem axisSegmentPoint_meeting_proper (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) (x : Plane)
    (hx : x ∈ openSegmentTrace (0,a) (b,0)) (hy : x ∈ openSegmentTrace (0,c) (d,0)) :
    ProperCrossing (openSegmentTrace (0,a) (b,0)) (openSegmentTrace (0,c) (d,0)) x := by
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint a b t=axisSegmentPoint c d u := he.trans hf.symm
  exact properCrossing_openSegments _ _ _ _ _ (axisSegmentPoint_meeting_det a b c d t u ha hb hne hmeet)
    ⟨t,ht,he⟩ ⟨u,hu,hf⟩

end Zarankiewicz

end

end OAI
