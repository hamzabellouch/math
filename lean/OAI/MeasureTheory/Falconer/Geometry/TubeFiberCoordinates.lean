import OAI.MeasureTheory.Falconer.Incidence.PencilDirections

namespace OAI

/-! Projection of a regular point fiber along its incident tube. The
coordinate set consists of original horizontal coordinates. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem tube_point_coordinate_fiber_card {δ : ℝ} (hδ : 0 < δ) (l : Space 2)
    (hl : |l 0| ≤ 1) (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) (a : ℝ) :
    ((P.filter fun p => p 0 = a).card:ℝ) ≤ 25 := by
  let S := P.filter fun p => p 0 = a
  let z := rowPoint a (l 0*a+l 1)
  have hwithin : ∀ p ∈ S, dist p z ≤ 2*δ := by
    intro p hp
    obtain ⟨hpP,hp0⟩ := Finset.mem_filter.mp hp
    rw [row_dist_projection hp0]
    have hh := tube_residual_le hδ.le hl (hinc p hpP)
    change |p 1-(l 0*a+l 1)| ≤ 2*δ
    convert hh using 1
    rw [hp0]
    congr 1
    ring
  have hb := separated_ball_card S z hδ (r := 2*δ) (by positivity)
    (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hwithin
  have he : (2*(2*δ)/δ+1)^2 = (25:ℝ) := by field_simp; ring
  rwa [he] at hb

theorem tube_point_coordinate_card {δ : ℝ} (hδ : 0 < δ) (l : Space 2)
    (hl : |l 0| ≤ 1) (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) :
    (P.card:ℝ) ≤ 25*((P.image fun p => p 0).card:ℝ) := by
  have hh := card_le_image_card_mul_fiber_bound P (fun p => p 0)
    (fun a _ => tube_point_coordinate_fiber_card hδ l hl P hsep hinc a)
  simpa only [mul_comm] using hh

theorem tube_point_strip_card {δ r s K u : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (P : Finset (Space 2)) (hinc : ∀ p ∈ P, TubeIncident δ p l)
    (hreg : NormalizedFiniteBallBound δ s K P) :
    ((P.filter fun p => |p 0-u| ≤ r).card:ℝ) ≤ K*(4*r)^s*(P.card:ℝ) := by
  let z := rowPoint u (l 0*u+l 1)
  have hsub : P.filter (fun p => |p 0-u| ≤ r) ⊆ P.filter (fun p => dist p z ≤ 4*r) := by
    intro p hp
    obtain ⟨hpP,hpu⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpP,?_⟩
    have hres := tube_residual_le hδ.le hl (hinc p hpP)
    have hres' : |p 1-(l 0*p 0+l 1)| ≤ 2*δ := by convert hres using 1; congr 1; ring
    have hprod : |(l 0*p 0+l 1)-(l 0*u+l 1)| ≤ r := by
      rw [show (l 0*p 0+l 1)-(l 0*u+l 1) = l 0*(p 0-u) by ring,abs_mul]
      exact (mul_le_mul hl hpu (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul r)
    have h1 : |p 1-(l 0*u+l 1)| ≤ 3*r := by
      have hh := (abs_sub_le (p 1) (l 0*p 0+l 1) (l 0*u+l 1)).trans (add_le_add hres' hprod)
      linarith only [hh,hr]
    have hd := planar_dist_le_coordinate_sum p z
    change dist p z ≤ |p 0-u|+|p 1-(l 0*u+l 1)| at hd
    linarith only [hd,hpu,h1]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (normalized_ball_bound_all_radii hs hK hreg z (4*r) (by linarith only [hr,hδ]))

theorem tube_point_coordinates_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K P) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (P.image fun p => p 0) u r ≤
        (25*K*(4:ℝ)^s)*r^s*((P.image fun p => p 0).card:ℝ) := by
  intro u r hr _
  have hsub : (P.image fun p => p 0).filter (fun a => |a-u| ≤ r) ⊆
      (P.filter fun p => |p 0-u| ≤ r).image (fun p => p 0) := by
    intro a ha
    obtain ⟨haP,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp haP
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,har⟩,rfl⟩
  have hc := tube_point_coordinate_card hδ l hl P hsep hinc
  have hr0 : 0 ≤ r := hδ.le.trans hr
  calc
    _ ≤ ((P.filter fun p => |p 0-u| ≤ r).card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(4*r)^s*(P.card:ℝ) := tube_point_strip_card hδ hr hs hK l hl P hinc hreg
    _ ≤ K*(4*r)^s*(25*((P.image fun p => p 0).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0]; ring

end Falconer

end OAI
