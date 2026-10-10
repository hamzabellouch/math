import OAI.MeasureTheory.Falconer.Geometry.ProjectionRatioGeometry
import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioFamily

namespace OAI

/-! Original direction-set ball counts survive the actual fractional-linear
coefficient map, with explicit cardinality and separation losses. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem projectionRatio_ball_bound {δ α s K C A a b : ℝ}
    (hα : 0 < α) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hab : b ≠ a) (hb : |b| ≤ 1) (hscale : δ ≤ C*α) (hsep : 8/|b-a| ≤ C)
    (I J : Finset ℝ) (hJI : J ⊆ I) (hJavoid : ∀ y ∈ J, y ≠ b)
    (hIbound : ∀ y ∈ I, |y| ≤ 1) (hsize : (I.card:ℝ) ≤ A*(J.card:ℝ))
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^s*(I.card:ℝ)) :
    ∀ u r : ℝ, α ≤ r → scalarBallMass (J.image (projectionRatio a b)) u r ≤
      (A*K*C^s)*r^s*((J.image (projectionRatio a b)).card:ℝ) := by
  classical
  let f := projectionRatio a b
  have hinj : Set.InjOn f (J:Set ℝ) := (projectionRatio_injOn hab).mono hJavoid
  have hcard : (J.image f).card = J.card := Finset.card_image_of_injOn hinj
  intro u r hr
  have hr0 : 0 < r := hα.trans_le hr
  let F := (J.image f).filter fun v => |v-u| ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨v,hv⟩ := hF
    obtain ⟨hv,hvu⟩ := Finset.mem_filter.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hsub : F ⊆ (I.filter fun z => |z-y| ≤ C*r).image f := by
      intro w hw
      obtain ⟨hw,hwu⟩ := Finset.mem_filter.mp hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hJI hz,?_⟩,rfl⟩
      have hd : |f z-f y| ≤ 2*r := by
        have hh := abs_sub_le (f z) u (f y)
        rw [abs_sub_comm u (f y)] at hh
        linarith
      have hi := projectionRatio_inverse_bound hab (hJavoid z hz) (hJavoid y hy)
        hb (hIbound z (hJI hz)) (hIbound y (hJI hy))
      have hL : 0 ≤ 4/|b-a| := by positivity
      have hm := mul_le_mul_of_nonneg_left hd hL
      have hCr := mul_le_mul_of_nonneg_right hsep hr0.le
      change |z-y| ≤ C*r
      change |z-y| ≤ (4/|b-a|)*|f z-f y| at hi
      calc
        _ ≤ (4/|b-a|)*(2*r) := hi.trans hm
        _ = (8/|b-a|)*r := by ring
        _ ≤ C*r := hCr
    have hc : (F.card:ℝ) ≤ scalarBallMass I y (C*r) := by
      change (F.card:ℝ) ≤ ((I.filter fun z => |z-y| ≤ C*r).card:ℝ)
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    have hdr : δ ≤ C*r := hscale.trans (mul_le_mul_of_nonneg_left hr hC)
    have hbound := scalar_ball_bound_all_radii hK hs I hball y (C*r) hdr
    have hm := mul_le_mul_of_nonneg_left hsize (show 0 ≤ K*(C*r)^s by positivity)
    rw [Real.mul_rpow hC hr0.le] at hbound hm
    change (F.card:ℝ) ≤ _
    rw [hcard]
    calc
      _ ≤ scalarBallMass I y (C*r) := hc
      _ ≤ K*(C^s*r^s)*(I.card:ℝ) := hbound
      _ ≤ K*(C^s*r^s)*(A*(J.card:ℝ)) := hm
      _ = _ := by ring
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
