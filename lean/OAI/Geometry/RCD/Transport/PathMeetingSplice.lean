import OAI.Geometry.RCD.Transport.LastPathAgreement
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Splicing equal-speed geodesics at a meeting point -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def splicePathAt (t : Time) (γ ζ : C(Time,X)) (h : γ t=ζ t) : C(Time,X) where
  toFun s := if s ≤ t then γ s else ζ s
  continuous_toFun := γ.continuous.if_le ζ.continuous continuous_id continuous_const
    (fun s hs => by simpa only [hs] using h)

theorem splicePathAt_left (t : Time) (γ ζ : C(Time,X)) (h : γ t=ζ t)
    {s : Time} (hs : s ≤ t) : splicePathAt t γ ζ h s=γ s := by
  simp [splicePathAt,hs]

theorem splicePathAt_right (t : Time) (γ ζ : C(Time,X)) (h : γ t=ζ t)
    {s : Time} (hs : t ≤ s) : splicePathAt t γ ζ h s=ζ s := by
  rcases eq_or_lt_of_le hs with he | he
  · subst s
    simpa [splicePathAt] using h
  · simp [splicePathAt,not_le.mpr he]

theorem splicePathAt_zero (t : Time) (γ ζ : C(Time,X)) (h : γ t=ζ t) :
    splicePathAt t γ ζ h 0=γ 0 :=
  splicePathAt_left t γ ζ h t.property.1

theorem splicePathAt_one (t : Time) (γ ζ : C(Time,X)) (h : γ t=ζ t) :
    splicePathAt t γ ζ h 1=ζ 1 :=
  splicePathAt_right t γ ζ h t.property.2

theorem geodesic_length_eq_of_meeting {γ ζ : C(Time,X)}
    (hγ : IsGeodesic γ) (hζ : IsGeodesic ζ) (h0 : γ 0=ζ 0)
    {t : Time} (ht : 0<(t:ℝ)) (he : γ t=ζ t) :
    dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1) := by
  have hg := hγ 0 t
  have hz := hζ 0 t
  change dist (γ 0) (γ t) = |0-(t:ℝ)| * dist (γ 0) (γ 1) at hg
  change dist (ζ 0) (ζ t) = |0-(t:ℝ)| * dist (ζ 0) (ζ 1) at hz
  rw [h0,he] at hg
  rw [zero_sub,abs_neg,abs_of_pos ht] at hg hz
  rw [h0]
  nlinarith

theorem splicePathAt_isGeodesic (t : Time) (γ ζ : C(Time,X)) (he : γ t=ζ t)
    (hγ : IsGeodesic γ) (hζ : IsGeodesic ζ) (h0 : γ 0=ζ 0)
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
  rw [splicePathAt_zero,splicePathAt_one,h0]
  rcases le_total s u with hsu | hus
  · rw [abs_sub_comm (s:ℝ) (u:ℝ),
      abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (u:ℝ) from hsu))]
    exact hordered s u hsu
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (u:ℝ) ≤ (s:ℝ) from hus)),dist_comm]
    exact hordered u s hus

end RegularPointCoordinates

end

end OAI
