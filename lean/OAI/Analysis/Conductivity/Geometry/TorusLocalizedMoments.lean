import Mathlib
import OAI.Analysis.Conductivity.Sources.TorusMoments

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma torus_band_integral_congr {T a b : ℝ} (hab : a≤b) {f g : Coord3 → ℝ}
    (h : ∀ x,x 0∈Icc a b  →  f x=g x) :
    (∫ t in a..b,torusCellIntegral T f t)=∫ t in a..b,torusCellIntegral T g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc a b := by simpa only [uIcc_of_le hab] using ht
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  exact h ![t,y,z] ht'

theorem periodic_localized_source_moment_formula {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ} {r : Fin 2 → Coord3 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hHp : AngularPeriodic T H) (hup : AngularPeriodic T u) (hHs : ∀ x,(H x).IsSymm)
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc a b})
    (hre : ∀ j x,x 0∈Icc a b  →  r j x=symmetricSource H u j x) :
    periodicSourceMoment T u r=
      ![torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) a,
        torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) a,
        torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) b-
          torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) a] := by
  have hmain (j : Fin 2) := (torus_full_integral_eq_band hab (hrs j)).trans
    ((torus_band_integral_congr (T:=T) hab (hre j)).trans
      (torus_band_divergence hT hab (symmetricFlux_smooth hH hu j) (symmetricFlux_periodic hHp hup j)))
  have hts : tsupport (fun x => u x 1*r 0 x-u x 0*r 1 x)⊆{x | x 0∈Icc a b} :=
    (tsupport_sub _ _).trans (union_subset
      (tsupport_mul_subset_right.trans (hrs 0)) (tsupport_mul_subset_right.trans (hrs 1)))
  have hc := torus_full_integral_eq_band (T:=T) hab hts
  have he := torus_band_integral_congr (T:=T) hab (f:=fun x => u x 1*r 0 x-u x 0*r 1 x)
    (g:=coordinateDivergence (symmetricCrossFlux H u)) (fun x hx => by
      rw [symmetricCrossFlux_divergence hH hu hHs,hre 0 x hx,hre 1 x hx])
  have hd := torus_band_divergence hT hab (symmetricCrossFlux_smooth hH hu)
    (symmetricCrossFlux_periodic hHp hup)
  ext i
  fin_cases i
  · exact hmain 0
  · exact hmain 1
  · exact hc.trans (he.trans hd)

end ScalarConductivity

end
end

end OAI
