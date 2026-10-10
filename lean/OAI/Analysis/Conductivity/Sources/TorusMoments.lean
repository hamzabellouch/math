import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularLocalizedMoments
import OAI.Analysis.Conductivity.Flux.TorusBoxFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_smul {f : Coord3 → ℝ} {F : Coord3 → Coord3}
    (hf : Differentiable ℝ f) (hF : Differentiable ℝ F) (x : Coord3) :
    coordinateDivergence (fun y => f y • F y) x=
      f x*coordinateDivergence F x+fderiv ℝ f x (F x) := by
  have he (i : Fin 3) :
      fderiv ℝ (fun y => (f y • F y) i) x (Pi.single i 1)=
        f x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)+
        F x i*fderiv ℝ f x (Pi.single i 1) := by
    change fderiv ℝ (fun y => f y*F y i) x _=_
    rw [fderiv_fun_mul (hf x) ((hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).differentiableAt)]
    rfl
  simp only [coordinateDivergence,he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [←coordinate_fderiv_expansion]

lemma coordinateDivergence_sub {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : Coord3) :
    coordinateDivergence (fun y => F y-G y) x=coordinateDivergence F x-coordinateDivergence G x := by
  unfold coordinateDivergence
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => F y i-G y i) x _=_
  rw [fderiv_fun_sub ((hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).differentiableAt)
    ((hasFDerivAt_pi'.mp (hG x).hasFDerivAt i).differentiableAt)]
  rfl

def symmetricCrossFlux (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : Coord3 :=
  u x 1 • (H x*gradientColumns (fderiv ℝ u x)).col 0-
    u x 0 • (H x*gradientColumns (fderiv ℝ u x)).col 1

lemma symmetricCrossFlux_smooth {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (symmetricCrossFlux H u) :=
  (((contDiff_pi.mp hu) 1).smul (symmetricFlux_smooth hH hu 0)).sub
    (((contDiff_pi.mp hu) 0).smul (symmetricFlux_smooth hH hu 1))

lemma symmetricCrossFlux_divergence {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hs : ∀ x,(H x).IsSymm) (x : Coord3) :
    coordinateDivergence (symmetricCrossFlux H u) x=
      u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x := by
  have huj (j : Fin 2) := ((contDiff_pi.mp hu) j).differentiable (by simp)
  have hF (j : Fin 2) := (symmetricFlux_smooth hH hu j).differentiable (by simp)
  unfold symmetricCrossFlux
  rw [coordinateDivergence_sub
    (F:=fun y => u y 1 • (H y*gradientColumns (fderiv ℝ u y)).col 0)
    (G:=fun y => u y 0 • (H y*gradientColumns (fderiv ℝ u y)).col 1)
    ((huj 1).smul (hF 0)) ((huj 0).smul (hF 1)),
    coordinateDivergence_smul (huj 1) (hF 0),coordinateDivergence_smul (huj 0) (hF 1),
    potential_component_fderiv (hu.differentiable (by simp)),
    potential_component_fderiv (hu.differentiable (by simp)),symmetric_potential_pairing _ _ (hs x)]
  unfold symmetricSource
  ring

lemma symmetricFlux_periodic {T : ℝ} {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : AngularPeriodic T H) (hu : AngularPeriodic T u) (j : Fin 2) :
    AngularPeriodic T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) := by
  intro n x
  dsimp only
  rw [hH n x,hu.fderiv n x]

lemma symmetricCrossFlux_periodic {T : ℝ} {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : AngularPeriodic T H) (hu : AngularPeriodic T u) :
    AngularPeriodic T (symmetricCrossFlux H u) := by
  intro n x
  unfold symmetricCrossFlux
  rw [hH n x,hu n x,hu.fderiv n x]

lemma torus_full_integral_eq_band {T a b : ℝ} (hab : a≤b) {f : Coord3 → ℝ}
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    (∫ t,torusCellIntegral T f t)=∫ t in a..b,torusCellIntegral T f t := by
  rw [intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz (y z : ℝ) : f ![t,y,z]=0 := by
    by_contra hh
    exact ht (hs (subset_tsupport f hh))
  simp only [torusCellIntegral,hz,intervalIntegral.integral_zero]

theorem periodic_symmetric_source_moment_formula {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hHp : AngularPeriodic T H) (hup : AngularPeriodic T u) (hHs : ∀ x,(H x).IsSymm)
    (hrs : ∀ j,tsupport (symmetricSource H u j)⊆{x | x 0∈Icc a b}) :
    periodicSourceMoment T u (symmetricSource H u)=
      ![torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) a,
        torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) a,
        torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) b-
          torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) a] := by
  have hmain (j : Fin 2) := (torus_full_integral_eq_band hab (hrs j)).trans
    (torus_band_divergence hT hab (symmetricFlux_smooth hH hu j) (symmetricFlux_periodic hHp hup j))
  have hts : tsupport (fun x => u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)⊆
      {x | x 0∈Icc a b} :=
    (tsupport_sub _ _).trans (union_subset
      (tsupport_mul_subset_right.trans (hrs 0)) (tsupport_mul_subset_right.trans (hrs 1)))
  have hc := (torus_full_integral_eq_band (T:=T) hab hts)
  have hd := torus_band_divergence hT hab (symmetricCrossFlux_smooth hH hu)
    (symmetricCrossFlux_periodic hHp hup)
  have hdiv : coordinateDivergence (symmetricCrossFlux H u)=
      (fun x => u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x) :=
    funext (symmetricCrossFlux_divergence hH hu hHs)
  rw [hdiv] at hd
  ext i
  fin_cases i
  · exact hmain 0
  · exact hmain 1
  · exact hc.trans hd

end ScalarConductivity

end
end

end OAI
