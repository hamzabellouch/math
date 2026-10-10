import OAI.Combinatorics.Crossing.BalancedAxisDrawing
import OAI.Combinatorics.Crossing.BalancedRayPairs

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem positive_scaled_eq_sign (a b t u : ℝ) (ht : 0 < t) (hu : 0 < u) (he : t*a=u*b) :
    (0 < a ↔ 0 < b) := by
  have hh : (0 < t*a ↔ 0 < a) := mul_pos_iff_of_pos_left ht
  have hh' : (0 < u*b ↔ 0 < b) := mul_pos_iff_of_pos_left hu
  rw [he] at hh
  exact hh.symm.trans hh'

theorem axis_meeting_abs_order (a b c d t u : ℝ)
    (ha : 0 < |a|) (hd : 0 < |d|) (hac : |a| < |c|)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (he : axisSegmentPoint a b t=axisSegmentPoint c d u) : |d| < |b| := by
  have hx := congrArg (fun z : Plane => |z.1|) he
  have hy := congrArg (fun z : Plane => |z.2|) he
  simp only [axisSegmentPoint_coordinates,abs_mul,abs_of_pos ht.1,abs_of_pos hu.1,
    abs_of_pos (sub_pos.mpr ht.2),abs_of_pos (sub_pos.mpr hu.2)] at hx hy
  have htu : t < u := by
    by_contra hnot
    have hgap := mul_pos (sub_pos.mpr hac) (sub_pos.mpr hu.2)
    have hdiff := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) ha.le
    nlinarith
  have hgap := mul_pos (sub_pos.mpr htu) hd
  have htb : t*(|b|-|d|) > 0 := by nlinarith [hx]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left ht.1).mp htb)

namespace BalancedAxisRealization
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem meeting_same_rays (i k : Fin m) (p q : Fin n) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) :
    (i.val < m/2 ↔ k.val < m/2) ∧ (p.val < n/2 ↔ q.val < n/2) := by
  rw [R.drawing_edgeInterior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (R.vertical i) (R.horizontal p) t=
      axisSegmentPoint (R.vertical k) (R.horizontal q) u := he.trans hf.symm
  have hcoordx := congrArg Prod.fst hmeet
  have hcoordy := congrArg Prod.snd hmeet
  simp only [axisSegmentPoint_coordinates] at hcoordx hcoordy
  have hposx := positive_scaled_eq_sign _ _ _ _ ht.1 hu.1 hcoordx
  have hposy := positive_scaled_eq_sign _ _ _ _ (sub_pos.mpr ht.2) (sub_pos.mpr hu.2) hcoordy
  exact ⟨(axisInterval_sign m i _ (R.vertical_interval i)).1.symm.trans
      (hposy.trans (axisInterval_sign m k _ (R.vertical_interval k)).1),
    (axisInterval_sign n p _ (R.horizontal_interval p)).1.symm.trans
      (hposx.trans (axisInterval_sign n q _ (R.horizontal_interval q)).1)⟩

theorem meeting_reverse_horizontal_order (i k : Fin m) (p q : Fin n) (hik : i < k) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) : q < p := by
  rw [R.drawing_edgeInterior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (R.vertical i) (R.horizontal p) t=
      axisSegmentPoint (R.vertical k) (R.horizontal q) u := he.trans hf.symm
  have hh := axis_meeting_abs_order _ _ _ _ t u (abs_pos.mpr (R.vertical_ne_zero i))
    (abs_pos.mpr (R.horizontal_ne_zero q)) (R.vertical_abs_strictMono hik) ht hu hmeet
  by_contra hnot
  have hle := R.horizontal_abs_strictMono.monotone (le_of_not_gt hnot)
  exact not_lt_of_ge hle hh

theorem meeting_balanced_pairs (i k : Fin m) (p q : Fin n) (hik : i < k) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) :
    (i,k) ∈ balancedRayPairs m ∧ (q,p) ∈ balancedRayPairs n := by
  obtain ⟨hvert,hhor⟩ := R.meeting_same_rays i k p q x hx hy
  exact ⟨(mem_balancedRayPairs m i k).mpr ⟨hik,hvert⟩,
    (mem_balancedRayPairs n q p).mpr ⟨R.meeting_reverse_horizontal_order i k p q hik x hx hy,hhor.symm⟩⟩

end BalancedAxisRealization
end Zarankiewicz

end

end OAI
