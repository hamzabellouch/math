import OAI.Geometry.CylinderCovering.Cartesian.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.Caps

namespace OAI

open Set
namespace CylinderCovering.CartesianCaps

lemma interval_subset_unit {D : AngularGeneral.Data}
    (hnodes : ∀ j ≤ D.count, |D.node j| ≤ 1) {j : ℕ} (hj : j < D.count) :
    AngularGeneral.interval D j ⊆ Icc (-1 : ℝ) 1 := by
  intro q hq
  have hl := abs_le.mp (hnodes j hj.le)
  have hr := abs_le.mp (hnodes (j+1) (by omega))
  exact ⟨hl.1.trans hq.1, hq.2.trans hr.2⟩

theorem cartesian_admissible (τ η E : ℝ) (D : AngularGeneral.Data)
    (hτ : τ ∈ Icc (0 : ℝ) (1/4)) (hη : η ∈ Ioc (0 : ℝ) 1)
    (hD : AngularGeneral.Admissible τ η E D) :
    AngularGeneral.Admissible τ η (max E 12) (withCartesianCaps τ η D) := by
  rcases hD with ⟨hn, hzero, hlast, hstrict, hnodes, hboundary, hcontinuous, hpositive, herr⟩
  refine ⟨hn, hzero, hlast, hstrict, hnodes, hboundary, ?_, ?_, ?_⟩
  · intro j hj
    exact (cap_continuousOn τ η hτ hη).mono (interval_subset_unit hnodes hj)
  · intro j hj q hq
    have haq : |q| ≤ 1 := abs_le.mpr (interval_subset_unit hnodes hj hq)
    have h := (cap_spec τ η q hτ hη haq).1.1
    change 0 < cap τ η q
    linarith
  · intro j hj q hq
    have hqD : q ∈ AngularGeneral.interval D j := hq
    have he := herr j hj q hqD
    have hE := mul_le_mul_of_nonneg_right (le_max_left E 12) (sq_nonneg τ)
    have h12 := mul_le_mul_of_nonneg_right (le_max_right E 12) (show 0 ≤ τ^4 by positivity)
    have haq : |q| ≤ 1 := abs_le.mpr (interval_subset_unit hnodes hj hqD)
    refine ⟨he.1.trans hE, he.2.1.trans hE, ?_⟩
    exact (cap_fourth_order τ η q hτ hη haq).trans h12

lemma cartesian_lowerIntercept (τ η b : ℝ) (D : AngularGeneral.Data)
    (hτ : τ ∈ Icc (0 : ℝ) (1/4)) (hη : η ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Icc (3/4 : ℝ) 1) (hnodes : ∀ j ≤ D.count, |D.node j| ≤ 1)
    (j : ℕ) (hj : j < D.count) :
    AngularGeneral.lowerIntercept (withCartesianCaps τ η D) j =
      {z | ∃ q ∈ AngularGeneral.interval D j, ∃ s ∈ aperture τ η b q,
        z = TriangularCovering.point 0 (q*s) s} := by
  ext z
  change (∃ q ∈ AngularGeneral.interval D j, ∃ s ∈ Icc 0 (cap τ η q),
    z = TriangularCovering.point 0 (q*s) s) ↔ _
  constructor
  · rintro ⟨q,hq,s,hs,hz⟩
    refine ⟨q,hq,s,?_,hz⟩
    rwa [aperture_eq_Icc τ η b q hτ hη hb (abs_le.mpr (interval_subset_unit hnodes hj hq))]
  · rintro ⟨q,hq,s,hs,hz⟩
    refine ⟨q,hq,s,?_,hz⟩
    rw [aperture_eq_Icc τ η b q hτ hη hb (abs_le.mpr (interval_subset_unit hnodes hj hq))] at hs
    exact hs

lemma cartesian_upperIntercept (τ η b : ℝ) (D : AngularGeneral.Data)
    (hτ : τ ∈ Icc (0 : ℝ) (1/4)) (hη : η ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Icc (3/4 : ℝ) 1) (hnodes : ∀ j ≤ D.count, |D.node j| ≤ 1)
    (j : ℕ) (hj : j < D.count) :
    AngularGeneral.upperIntercept (withCartesianCaps τ η D) j =
      {z | ∃ q ∈ AngularGeneral.interval D j, ∃ s ∈ aperture τ η b q,
        z = TriangularCovering.point (q*s) 0 (1-s)} := by
  ext z
  change (∃ q ∈ AngularGeneral.interval D j, ∃ s ∈ Icc 0 (cap τ η q),
    z = TriangularCovering.point (q*s) 0 (1-s)) ↔ _
  constructor
  · rintro ⟨q,hq,s,hs,hz⟩
    refine ⟨q,hq,s,?_,hz⟩
    rwa [aperture_eq_Icc τ η b q hτ hη hb (abs_le.mpr (interval_subset_unit hnodes hj hq))]
  · rintro ⟨q,hq,s,hs,hz⟩
    refine ⟨q,hq,s,?_,hz⟩
    rw [aperture_eq_Icc τ η b q hτ hη hb (abs_le.mpr (interval_subset_unit hnodes hj hq))] at hs
    exact hs

end CylinderCovering.CartesianCaps

end OAI
