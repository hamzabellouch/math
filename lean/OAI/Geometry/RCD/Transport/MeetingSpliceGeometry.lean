import OAI.Geometry.RCD.Transport.PathMeetingSplice
import OAI.Geometry.RCD.Transport.ContactCrossLength

namespace OAI

/-! # Splicing arbitrary contacting geodesics at an interior meeting -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem splicePathAt_isGeodesic_of_cross_length (t : Time) (γ ζ : C(Time,X)) (he : γ t=ζ t)
    (hγ : IsGeodesic γ) (hζ : IsGeodesic ζ)
    (hcross : dist (γ 0) (ζ 1)=dist (ζ 0) (ζ 1))
    (hlen : dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1)) :
    IsGeodesic (splicePathAt t γ ζ he) := by
  have hordered (s u : Time) (hsu : s ≤ u) :
      dist (splicePathAt t γ ζ he s) (splicePathAt t γ ζ he u) ≤
        ((u:ℝ)-(s:ℝ))*dist (ζ 0) (ζ 1) := by
    by_cases hut : u ≤ t
    · rw [splicePathAt_left t γ ζ he (hsu.trans hut),splicePathAt_left t γ ζ he hut,
        hγ,hlen,abs_sub_comm (s:ℝ) (u:ℝ),
        abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (u:ℝ) from hsu))]
    by_cases hts : t ≤ s
    · rw [splicePathAt_right t γ ζ he hts,splicePathAt_right t γ ζ he (hts.trans hsu),
        hζ,abs_sub_comm (s:ℝ) (u:ℝ),
        abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (u:ℝ) from hsu))]
    have hst : s ≤ t := (lt_of_not_ge hts).le
    have htu : t ≤ u := (lt_of_not_ge hut).le
    rw [splicePathAt_left t γ ζ he hst,splicePathAt_right t γ ζ he htu]
    calc
      dist (γ s) (ζ u) ≤ dist (γ s) (γ t)+dist (γ t) (ζ u) := dist_triangle _ _ _
      _ = ((t:ℝ)-(s:ℝ))*dist (ζ 0) (ζ 1)+((u:ℝ)-(t:ℝ))*dist (ζ 0) (ζ 1) := by
        rw [hγ,he,hζ,hlen,abs_sub_comm (s:ℝ) (t:ℝ),
          abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst)),abs_sub_comm (t:ℝ) (u:ℝ),
          abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ (u:ℝ) from htu))]
      _ = _ := by ring
  apply isGeodesic_of_dist_le
  intro s u
  rw [splicePathAt_zero,splicePathAt_one,hcross]
  rcases le_total s u with hsu | hus
  · rw [abs_sub_comm (s:ℝ) (u:ℝ),
      abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (u:ℝ) from hsu))]
    exact hordered s u hsu
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (u:ℝ) ≤ (s:ℝ) from hus)),dist_comm]
    exact hordered u s hus


theorem contacting_splice_isGeodesic {φ ψ : X → ℝ}
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {γ ζ : C(Time,X)} (hg : IsGeodesic γ) (hz : IsGeodesic ζ)
    (hγ : φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hζ : φ (ζ 0)+ψ (ζ 1)=dist (ζ 0) (ζ 1)^2/2)
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) (hmeet : γ t=ζ t) :
    IsGeodesic (splicePathAt t γ ζ hmeet) := by
  have hlen := contacting_geodesics_equal_length had hg hz hγ hζ ht0 ht1 hmeet
  have hcross := (contacting_geodesics_cross_length had hg hz hγ hζ ht0 ht1 hmeet).1
  exact splicePathAt_isGeodesic_of_cross_length t γ ζ hmeet hg hz (hcross.trans hlen) hlen

end RegularPointCoordinates

end

end OAI
