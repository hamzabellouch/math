import OAI.Analysis.AncientFlat.Geometry.WindowSchauder
import OAI.Analysis.AncientFlat.Geometry.ParabolicAverage

namespace OAI
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicInterpolation ParabolicAverage
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma box_subset_cylinder (r R q : ℝ) (hr : 0≤r) (hq : 0<q) (hgap : r+q≤R)
    (p : V × ℝ) (hp : p∈cylinder r) : box p q⊆cylinder R := by
  have hpow : r^4+q^4≤R^4 := by
    have ha : r^4+q^4≤(r+q)^4 := by
      nlinarith [mul_nonneg (pow_nonneg hr 3) hq.le,mul_nonneg hr (pow_nonneg hq.le 3),sq_nonneg (r*q)]
    exact ha.trans (pow_le_pow_left₀ (by positivity) hgap 4)
  intro z hz
  have hx : ‖z.1-p.1‖<q := by simpa only [box,mem_prod,mem_ball,dist_eq_norm] using hz.1
  have ht : p.2-q^4<z.2 ∧ z.2≤p.2 := hz.2
  refine ⟨lt_of_le_of_lt (norm_le_insert' z.1 p.1) (by linarith [hp.1]),?_,ht.2.trans hp.2.2⟩
  linarith [hp.2.1]

omit [MeasurableSpace V] [BorelSpace V] in
lemma box_oscillation (r R q D : ℝ) (hr : 0≤r) (hq : 0<q) (hq1 : q≤1)
    (hgap : r+q≤R) (hD : 0≤D) (u ut : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hd : ∀ p∈cylinder R, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2)
    (hsp : ∀ p∈cylinder R, ‖iteratedFDeriv ℝ 1 (u p.2) p.1‖≤D)
    (htm : ∀ p∈cylinder R, ‖ut p.2 p.1‖≤D)
    (p : V × ℝ) (hp : p∈cylinder r) :
    ∀ z∈box p q, ‖u p.2 p.1-u z.2 z.1‖≤2*D*q := by
  have hsub : (cylinder r : Set (V × ℝ))⊆cylinder R := cylinder_mono hr (by linarith)
  have hpR := hsub hp
  intro z hz
  have hzR := box_subset_cylinder r R q hr hq hgap p hp hz
  have htime (t : ℝ) (ht : t∈uIcc z.2 p.2) : -(R^4)<t ∧ t≤0 := by
    rw [uIcc_of_le hz.2.2] at ht
    exact ⟨hzR.2.1.trans_le ht.1,ht.2.trans hpR.2.2⟩
  have ht := time_difference_bound u ut z.2 p.2 R D
    (fun t ht x hx => hd (x,t) ⟨hx,htime t ht⟩)
    (fun t ht x hx => htm (x,t) ⟨hx,htime t ht⟩) p.1 hpR.1
  have hx : ‖u z.2 p.1-u z.2 z.1‖≤D*‖p.1-z.1‖ := by
    apply (convex_ball (0:V) R).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (hs z.2).differentiable (by norm_num) x)
    · intro x hx
      rw [←norm_iteratedFDeriv_one]
      exact hsp (x,z.2) ⟨by simpa only [mem_ball,dist_zero_right] using hx,hzR.2⟩
    · simpa only [mem_ball,dist_zero_right] using hzR.1
    · simpa only [mem_ball,dist_zero_right] using hpR.1
  have hdt : |p.2-z.2|≤q^4 := by rw [abs_of_nonneg (sub_nonneg.mpr hz.2.2)]; linarith [hz.2.1]
  have hdx : ‖p.1-z.1‖≤q := by
    rw [norm_sub_rev]
    exact le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hz.1)
  have hq4 : q^4≤q := by simpa using pow_le_pow_of_le_one hq.le hq1 (by norm_num : (1:ℕ)≤4)
  calc
    ‖u p.2 p.1-u z.2 z.1‖≤‖u p.2 p.1-u z.2 p.1‖+‖u z.2 p.1-u z.2 z.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤q^4*D+D*q := add_le_add (ht.trans (mul_le_mul_of_nonneg_right hdt hD)) (hx.trans (mul_le_mul_of_nonneg_left hdx hD))
    _≤2*D*q := by nlinarith [mul_le_mul_of_nonneg_right hq4 hD]
end ParabolicLocalization

end

end OAI
