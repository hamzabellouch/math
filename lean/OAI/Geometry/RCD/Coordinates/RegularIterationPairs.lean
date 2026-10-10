import OAI.Geometry.RCD.Coordinates.RegularPairEndpoints
import OAI.Geometry.RCD.Coordinates.RegularNearbyFrozen
import OAI.Geometry.RCD.Coordinates.PairGeometry
import OAI.Geometry.RCD.Coordinates.RegularPatchIteration

namespace OAI

/-! # Actual pair and segment geometry for the coordinate iteration -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The inverse of the working chart transports the actual heat frames.
Endpoint separation and the segment estimates follow from approximation
and the ellipsoid preimages, rather than being extra geometric inputs. -/
theorem regular_iteration_pair_geometry {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzetaSmall : zeta ≤ 1 / 2048)
    (hgramSmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    {Ω : Set (Euclidean n)} (u : e.heat.patchRegion ≃ₜ Ω)
    (hu : ∀ q, (u q).val = e.heat.values q.val)
    (inverse : Euclidean n → {q : X // q ∈ ball base (e.heat.radius / 32)})
    (hinverse : ∀ x ∈ Ω, (inverse x).val ∈ e.heat.patchRegion ∧ e.heat.values (inverse x).val = x)
    {Theta Bjet δ : ℝ} (hTheta : 1 ≤ Theta) (hBjet : 1 ≤ Bjet)
    (hzetaL : zeta * iterationPairMultiplier Theta Bjet 64 ≤ 2097152)
    (hδ : δ ≤ e.heat.radius / 2 ^ (e.heat.shift + 12))
    (hdiam : 2 * iterationPairMultiplier Theta Bjet 64 * δ ≤
      distanceSourceRadius e.heat.radius e.heat.shift) :
    IterationPairGeometry
      (fun x : ball base δ => e.heat.values x.val) Ω
      (fun i x => e.heat.frozenAt (inverse x).val i)
      (distanceSourceRadius e.heat.radius e.heat.shift) Theta Bjet 64 := by
  let L := iterationPairMultiplier Theta Bjet 64
  have hL : 274877906944 ≤ L := by
    have hh := mul_le_mul hTheta hBjet zero_le_one (zero_le_one.trans hTheta)
    dsimp only [L, iterationPairMultiplier, iterationChartRatio]
    norm_num at hh ⊢
    nlinarith only [hh]
  have hL0 : 0 ≤ L := by linarith
  have hinside {x : X} (hx : x ∈ ball base δ) : x ∈ e.heat.patchRegion := by
    apply ball_subset_ball _ hx
    exact hδ.trans (div_le_div_of_nonneg_left e.heat.radius_pos.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega : e.heat.shift + 10 ≤ e.heat.shift + 12)))
  have hinv {x : X} (hx : x ∈ e.heat.patchRegion) :
      (inverse (e.heat.values x)).val = x :=
    working_chart_inverse_left e.heat u hu inverse hinverse hx
  apply iterationPairGeometry_of_all_scales
    (fun x : ball base δ => e.heat.values x.val) Ω
    (fun i x => e.heat.frozenAt (inverse x).val i)
    (distanceSourceRadius_pos e.heat.radius_pos _) hTheta hBjet (by norm_num)
  · intro x z
    have ht := dist_triangle x.val base z.val
    rw [dist_comm base z.val] at ht
    have hx : dist x.val base < δ := x.property
    have hz : dist z.val base < δ := z.property
    have hd : dist x.val z.val ≤ 2 * δ := by linarith
    have hh := mul_le_mul_of_nonneg_left hd hL0
    change L * dist x.val z.val ≤ _
    exact hh.trans (by calc
      L * (2 * δ) = 2 * L * δ := by ring
      _ ≤ _ := hdiam)
  · intro i x z hxz hlow hupp
    have hxi := hinside x.property
    have hzi := hinside z.property
    have hxz' : x.val ≠ z.val := fun hh => hxz (Subtype.ext hh)
    have ht : 0 < dist x.val z.val := dist_pos.mpr hxz'
    have hscale := iterationRadius_distanceSourceRadius e.heat.radius e.heat.shift i
    rw [hscale] at hlow hupp
    change L * dist x.val z.val ≤ distanceSourceRadius e.heat.radius (e.heat.shift + i) at hlow
    change distanceSourceRadius e.heat.radius (e.heat.shift + i) ≤ 2 * L * dist x.val z.val at hupp
    have he := e.heat.pair_endpoints_at_scale (by linarith : 2097152 ≤ L)
      hzeta hzetaL i (e.heat.patch_region_subset hxi) hlow hupp
    refine ⟨?_, ?_, ?_⟩
    · rw [hinv hxi]
      change (64 : ℝ)⁻¹ * dist x.val z.val ≤ _
      rw [show (64 : ℝ)⁻¹ = 1 / 64 by norm_num]
      linarith [he.1, ht]
    · rw [hinv hxi]
      change _ ≤ 64 * dist x.val z.val
      linarith [he.2, ht]
    apply segment_geometry_of_ellipsoid e.heat.values
      (fun P => e.heat.frozenAt (inverse P).val i)
      (x := x.val) (z := z.val) (r := regularEllipsoidRadius e.heat.radius e.heat.shift i)
      (c := 1 / 32) (W := e.heat.patchRegion)
    · rw [hinv hxi]
      have hs := source_eq_ellipsoidRadius e.heat.radius e.heat.shift i
      have hm := mul_lt_mul_of_pos_right (show (1073741824 : ℝ) < L by linarith) ht
      rw [hs] at hlow
      linarith [he.2]
    · intro P hP
      rw [hinv hxi] at hP
      have hroom := regular_ellipsoid_room e.heat.radius_pos e.heat.shift i
        (ball_subset_ball hδ x.property)
      obtain ⟨y, hy, hd, heq⟩ := regular_frozen_ellipsoid_preimages hX e hzeta hzetaSmall
        hgramSmall i hxi hroom P (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hP)
      refine ⟨?_, y, hy, hd, heq⟩
      rw [← heq, ← hu ⟨y, hy⟩]
      exact (u ⟨y, hy⟩).property
    · intro y hy hd w
      rw [hinv hy, hinv hxi]
      have hρ : regularEllipsoidRadius e.heat.radius e.heat.shift i ≤
          e.heat.radius / 2 ^ (e.heat.shift + i + 17) := by
        unfold regularEllipsoidRadius iterationRadius
        have heq : e.heat.radius / 128 / 2 ^ (e.heat.shift + i + 17) =
            (e.heat.radius / 2 ^ (e.heat.shift + i + 17)) / 128 := by ring
        rw [heq]
        have hr : 0 < e.heat.radius / 2 ^ (e.heat.shift + i + 17) :=
          div_pos e.heat.radius_pos (by positivity)
        linarith
      have hb := regular_nearby_frozen_bound hX e (e.heat.patch_region_subset hxi)
        (e.heat.patch_region_subset hy) hzeta hnear i
        (by rw [dist_comm]; exact hd.le.trans hρ) w
      linarith [norm_nonneg (e.heat.frozenAt x.val i w)]

end RegularPointCoordinates

end

end OAI
