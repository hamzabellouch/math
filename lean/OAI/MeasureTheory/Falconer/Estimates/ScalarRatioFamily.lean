import OAI.MeasureTheory.Falconer.Estimates.ScalarZoom

namespace OAI

/-! Counting and ball regularity for the actual ratio coefficients retained
by the common-rectangle selection. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_ball_bound_all_radii {δ s K : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s)
    (E : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ K*r^s*(E.card:ℝ))
    (u r : ℝ) (hr : δ ≤ r) : scalarBallMass E u r ≤ K*r^s*(E.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hball u r hr hr1
  · have hp : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr1) hs
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hc : scalarBallMass E u r ≤ (E.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hf : 1 ≤ K*r^s := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) E.card])

 theorem scalar_ratio_family_card {c : ℝ} (hc : c ≠ 0) (J : Finset ℝ) :
    (J.image (fun y => -y/c)).card = J.card := by
  apply Finset.card_image_of_injective
  intro x y h
  have hh := congrArg (fun a => a*c) h
  simp only [div_mul_cancel₀ _ hc] at hh
  linarith

 theorem scalar_ratio_family_ball {δ s K A M c : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hM : 1 ≤ M) (hc : c ≠ 0) (hcM : |c| ≤ M)
    (I J : Finset ℝ) (hJI : J ⊆ I) (hsize : (I.card:ℝ) ≤ A*(J.card:ℝ))
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^s*(I.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ r →
      scalarBallMass (J.image (fun y => -y/c)) u r ≤
        (A*K*M^s)*r^s*((J.image (fun y => -y/c)).card:ℝ) := by
  classical
  intro u r hr
  have hr0 : 0 < r := hδ.trans_le hr
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let F := I.filter fun y => |y-(-c*u)| ≤ M*r
  have hsub : (J.image (fun y => -y/c)).filter (fun a => |a-u| ≤ r) ⊆
      F.image (fun y => -y/c) := by
    intro a ha
    obtain ⟨ha,hnear⟩ := Finset.mem_filter.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hJI hy,?_⟩,rfl⟩
    have he : y-(-c*u) = -c*((-y/c)-u) := by field_simp; ring
    rw [he,abs_mul,abs_neg]
    exact mul_le_mul hcM hnear (abs_nonneg _) hM0
  have hcount : scalarBallMass (J.image (fun y => -y/c)) u r ≤ scalarBallMass I (-c*u) (M*r) := by
    change (((J.image (fun y => -y/c)).filter (fun a => |a-u| ≤ r)).card:ℝ) ≤ (F.card:ℝ)
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hdr : δ ≤ M*r := by nlinarith
  have hb := scalar_ball_bound_all_radii hK hs I hball (-c*u) (M*r) hdr
  have hm := mul_le_mul_of_nonneg_left hsize (show 0 ≤ K*(M*r)^s by positivity)
  rw [Real.mul_rpow hM0 hr0.le] at hb hm
  rw [scalar_ratio_family_card hc]
  calc
    _ ≤ scalarBallMass I (-c*u) (M*r) := hcount
    _ ≤ K*(M^s*r^s)*(I.card:ℝ) := hb
    _ ≤ K*(M^s*r^s)*(A*(J.card:ℝ)) := hm
    _ = _ := by ring

end Falconer

end OAI
