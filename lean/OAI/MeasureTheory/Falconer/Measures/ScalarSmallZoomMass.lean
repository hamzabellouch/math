import OAI.MeasureTheory.Falconer.Shells.ScalarPositiveZoom

namespace OAI

/-! Balls below the rescaled original resolution remain controlled by
 the exponent reserve in the original coefficient Frostman estimate. -/
namespace Falconer

 theorem scalarBallMass_radius_mono (E : Finset ℝ) (u : ℝ) {r s : ℝ} (h : r ≤ s) :
    scalarBallMass E u r ≤ scalarBallMass E u s := by
  unfold scalarBallMass
  have hs : E.filter (fun x => |x-u| ≤ r) ⊆ E.filter (fun x => |x-u| ≤ s) := by
    intro x hx
    obtain ⟨hxE,hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxE,hxr.trans h⟩
  exact_mod_cast Finset.card_le_card hs

 theorem scalar_positive_zoom_small_mass {δ κ K z R : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hR : 0 < R)
    (E F : Finset ℝ) (hFE : F ⊆ E)
    (hsize : (E.card:ℝ) ≤ (4:ℝ)^κ*K*(F.card:ℝ))
    (hweak : ∀ u : ℝ, scalarBallMass E u δ ≤ K*δ^(2*κ)*(E.card:ℝ))
    (hbudget : K^2*δ^κ ≤ 1) (u r : ℝ) (hr : δ ≤ r) (hsmall : 6*R*r ≤ δ) :
    scalarBallMass (scalarZoom (z-3*R) (6*R) F) u r ≤
      (12:ℝ)^κ*r^κ*((scalarZoom (z-3*R) (6*R) F).card:ℝ) := by
  rw [scalarZoom_ball_mass (by positivity),scalarZoom_card (by positivity)]
  have hp : δ^(2*κ) = (δ^κ)^2 := by
    rw [show 2*κ = κ+κ by ring,Real.rpow_add hδ,pow_two]
  have hδpow : 0 ≤ δ^κ := Real.rpow_nonneg hδ.le _
  have hpow : δ^κ ≤ r^κ := Real.rpow_le_rpow hδ.le hr hκ
  have hbase : (4:ℝ)^κ ≤ (12:ℝ)^κ := Real.rpow_le_rpow (by norm_num) (by norm_num) hκ
  calc
    _ ≤ scalarBallMass E (z-3*R+6*R*u) (6*R*r) := scalarBallMass_mono hFE _ _
    _ ≤ scalarBallMass E (z-3*R+6*R*u) δ := scalarBallMass_radius_mono E _ hsmall
    _ ≤ K*δ^(2*κ)*(E.card:ℝ) := hweak _
    _ ≤ K*δ^(2*κ)*((4:ℝ)^κ*K*(F.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg hδ.le _))
    _ = ((4:ℝ)^κ*δ^κ*(F.card:ℝ))*(K^2*δ^κ) := by rw [hp]; ring
    _ ≤ (4:ℝ)^κ*δ^κ*(F.card:ℝ) := by
      exact (mul_le_mul_of_nonneg_left hbudget (by positivity)).trans_eq (mul_one _)
    _ ≤ (12:ℝ)^κ*r^κ*(F.card:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hbase hpow hδpow (by positivity)) (Nat.cast_nonneg _)

end Falconer

end OAI
