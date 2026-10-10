import OAI.MeasureTheory.Falconer.Radial.ScalarAffineExceptions
import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioFamily
import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows

namespace OAI

/-! Finite Kaufman sublevel bound for the actual slope projections. This
is the geometric estimate used to find regular projections inside the
coarse tube packet, before extracting its product rows. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem finite_projection_sublevel {δ r s K : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hs : 0 ≤ s) (hK : 1 ≤ K) (I : Finset ℝ)
    (hI : ∀ c ∈ I, |c| ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass I u t ≤ K*t^s*(I.card:ℝ))
    (p q : Space 2) (hdiam : dist p q ≤ 4) :
    ((I.filter fun c => |lineParameterProjection c p-lineParameterProjection c q| ≤ r).card:ℝ) ≤
      K*(8*r/max (dist p q) δ)^s*(I.card:ℝ) := by
  let B := I.filter fun c => |lineParameterProjection c p-lineParameterProjection c q| ≤ r
  let D := max (dist p q) δ
  have hD : 0 < D := hδ.trans_le (le_max_right _ _)
  have hr0 : 0 < r := hδ.trans_le hr
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases hcoarse : D ≤ 8*r
  · have hratio : 1 ≤ 8*r/D := (le_div_iff₀ hD).2 (by simpa using hcoarse)
    have hpow : 1 ≤ (8*r/D)^s := Real.one_le_rpow hratio hs
    have hprod : 1 ≤ K*(8*r/D)^s := by
      simpa only [one_mul] using mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) hK0
    exact (Nat.cast_le.mpr (Finset.card_filter_le I _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg I.card))
  have hfar : 8*r < D := lt_of_not_ge hcoarse
  have hdδ : δ < dist p q := by
    by_contra hh
    have he : D = δ := max_eq_right (le_of_not_gt hh)
    rw [he] at hfar
    linarith only [hfar,hr,hδ]
  have heD : D = dist p q := max_eq_left hdδ.le
  have hd : 0 < dist p q := hδ.trans hdδ
  let u := p 1-q 1
  let v := p 0-q 0
  have he (c : ℝ) : lineParameterProjection c p-lineParameterProjection c q = u+c*v := by
    dsimp [lineParameterProjection,u,v]
    ring
  by_cases hB : B.Nonempty
  · obtain ⟨c,hc⟩ := hB
    obtain ⟨hcI,hcproj⟩ := Finset.mem_filter.mp hc
    rw [he] at hcproj
    have hcv : |c*v| ≤ |v| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hI c hcI) (abs_nonneg v)
    have hu : |u| ≤ r+|v| := by
      have hh : |u| ≤ |u+c*v|+|c*v| := by
        simpa only [add_sub_cancel_right] using abs_sub (u+c*v) (c*v)
      linarith only [hh,hcproj,hcv]
    have hdp : dist p q ≤ |v|+|u| := planar_dist_le_coordinate_sum p q
    have hv : dist p q/4 ≤ |v| := by rw [heD] at hfar; linarith only [hfar,hdp,hu,hd]
    have hμ : 0 < dist p q/4 := by positivity
    have hscale : δ ≤ r/(dist p q/4) := by
      apply (le_div_iff₀ hμ).2
      have hh := mul_le_mul_of_nonneg_left (show dist p q/4 ≤ 1 by linarith only [hdiam]) hδ.le
      have hh' : δ*(dist p q/4) ≤ δ := by simpa only [mul_one] using hh
      exact hh'.trans hr
    have hscale1 : r/(dist p q/4) ≤ 1 := by
      apply (div_le_one hμ).2
      rw [heD] at hfar
      linarith only [hfar,hr0]
    have hb := scalar_affine_small_card hμ hr0.le hscale hscale1 I hball (u := u) hv
    have heB : B = I.filter (fun c => |u+c*v| ≤ r) := by
      dsimp [B]
      simp_rw [he]
    rw [← heB] at hb
    have hrat : r/(dist p q/4) ≤ 8*r/D := by
      rw [heD]
      apply (div_le_div_iff₀ hμ hd).2
      nlinarith only [mul_nonneg hr0.le hd.le]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hrat hs) hK0)
      (Nat.cast_nonneg I.card))
  · have heB : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card:ℝ) ≤ _
    rw [heB,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
