import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows
import OAI.MeasureTheory.Falconer.Angular.AngularSamples
import OAI.MeasureTheory.Falconer.Recursion.FiniteCountingPotential
import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover
import OAI.MeasureTheory.Falconer.Angular.GoodProjectionDirections

namespace OAI

/-! Direction sets of separated pencils. The fixed multiplicity and
regularity costs are proved from the original point-line incidence. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem pencil_slope_fiber_card {δ : ℝ} (hδ : 0 < δ) (p : Space 2)
    (T : Finset (Space 2)) (hsep : FiniteSeparatedAt δ T)
    (hchart : InBoundedLineChart T) (hinc : ∀ l ∈ T, TubeIncident δ p l) (a : ℝ) :
    ((T.filter fun l => l 0 = a).card:ℝ) ≤ 25 := by
  let S := T.filter fun l => l 0 = a
  let z := rowPoint a (p 1-a*p 0)
  have hwithin : ∀ l ∈ S, dist l z ≤ 2*δ := by
    intro l hl
    obtain ⟨hlT,hl0⟩ := Finset.mem_filter.mp hl
    rw [row_dist_projection hl0]
    have hh := tube_residual_le hδ.le (hchart l hlT).1 (hinc l hlT)
    rw [hl0] at hh
    change |l 1-(p 1-a*p 0)| ≤ 2*δ
    rw [abs_sub_comm]
    exact hh
  have hb := separated_ball_card S z hδ (r := 2*δ) (by positivity)
    (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hwithin
  have he : (2*(2*δ)/δ+1)^2 = (25:ℝ) := by field_simp; ring
  rwa [he] at hb

theorem pencil_slope_card {δ : ℝ} (hδ : 0 < δ) (p : Space 2)
    (T : Finset (Space 2)) (hsep : FiniteSeparatedAt δ T)
    (hchart : InBoundedLineChart T) (hinc : ∀ l ∈ T, TubeIncident δ p l) :
    (T.card:ℝ) ≤ 25*((T.image fun l => l 0).card:ℝ) := by
  have hh := card_le_image_card_mul_fiber_bound T (fun l => l 0)
    (fun a _ => pencil_slope_fiber_card hδ p T hsep hchart hinc a)
  simpa only [mul_comm] using hh

theorem pencil_slope_strip_card {δ r s K u : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (hp : |p 0| ≤ 1)
    (T : Finset (Space 2)) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K T) :
    ((T.filter fun l => |l 0-u| ≤ r).card:ℝ) ≤ K*(4*r)^s*(T.card:ℝ) := by
  let z := rowPoint u (p 1-u*p 0)
  have hsub : T.filter (fun l => |l 0-u| ≤ r) ⊆ T.filter (fun l => dist l z ≤ 4*r) := by
    intro l hl
    obtain ⟨hlT,hlu⟩ := Finset.mem_filter.mp hl
    refine Finset.mem_filter.mpr ⟨hlT,?_⟩
    have hres := tube_residual_le hδ.le (hchart l hlT).1 (hinc l hlT)
    have hres' : |l 1-(p 1-l 0*p 0)| ≤ 2*δ := by
      rw [abs_sub_comm]
      exact hres
    have hprod : |(p 1-l 0*p 0)-(p 1-u*p 0)| ≤ r := by
      rw [show (p 1-l 0*p 0)-(p 1-u*p 0) = -(l 0-u)*p 0 by ring,abs_mul,abs_neg]
      exact (mul_le_mul hlu hp (abs_nonneg _) (hδ.le.trans hr)).trans_eq (mul_one r)
    have h1 : |l 1-(p 1-u*p 0)| ≤ 3*r := by
      have hh := (abs_sub_le (l 1) (p 1-l 0*p 0) (p 1-u*p 0)).trans (add_le_add hres' hprod)
      linarith only [hh,hr]
    have hd := planar_dist_le_coordinate_sum l z
    change dist l z ≤ |l 0-u|+|l 1-(p 1-u*p 0)| at hd
    linarith only [hd,hlu,h1]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (normalized_ball_bound_all_radii hs hK hreg z (4*r) (by linarith only [hr,hδ]))

theorem pencil_slope_regular {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (p : Space 2) (hp : |p 0| ≤ 1) (T : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ T) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K T) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (T.image fun l => l 0) u r ≤
        (25*K*(4:ℝ)^s)*r^s*((T.image fun l => l 0).card:ℝ) := by
  intro u r hr _
  have hsub : (T.image fun l => l 0).filter (fun a => |a-u| ≤ r) ⊆
      (T.filter fun l => |l 0-u| ≤ r).image (fun l => l 0) := by
    intro a ha
    obtain ⟨haT,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp haT
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,har⟩,rfl⟩
  have hc := pencil_slope_card hδ p T hsep hchart hinc
  have hr0 : 0 ≤ r := hδ.le.trans hr
  calc
    _ ≤ ((T.filter fun l => |l 0-u| ≤ r).card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(4*r)^s*(T.card:ℝ) := pencil_slope_strip_card hδ hr hs hK p hp T hchart hinc hreg
    _ ≤ K*(4*r)^s*(25*((T.image fun l => l 0).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0]; ring

end Falconer

end OAI
