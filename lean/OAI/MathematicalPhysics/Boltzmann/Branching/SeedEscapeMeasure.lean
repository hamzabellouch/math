import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

section

/-! # Uniform free-flight escape of the bounded nonaxial seed -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem seed_flight_bounds {n : ℕ} {p : Velocity × Velocity}
    (hp : p ∈ seedPortion n) {t : ℝ} (ht : 0 ≤ t) :
    t/((n : ℝ)+1)-(n : ℝ) ≤ ‖transverse (p.1+t • p.2)‖ ∧
      ‖p.1+t • p.2‖ ≤ (n : ℝ)*(1+t) := by
  have he : transverse (p.1+t • p.2) = transverse p.1+t • transverse p.2 := by
    apply (WithLp.ext_iff 2).mpr
    funext i
    rfl
  have hv := mul_le_mul_of_nonneg_left hp.2.2 ht
  have hn := norm_sub_norm_le (t • transverse p.2) (-transverse p.1)
  rw [sub_neg_eq_add,add_comm,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg] at hn
  have hx := (LargeOutput.transverse_norm_le p.1).trans hp.1
  have hupper := norm_add_le p.1 (t • p.2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at hupper
  have htv := mul_le_mul_of_nonneg_left hp.2.1 ht
  refine ⟨?_,by nlinarith [hp.1]⟩
  rw [he]
  have hd : t*(1/((n : ℝ)+1)) = t/((n : ℝ)+1) := by ring
  rw [hd] at hv
  linarith

theorem seed_flight_radius_linear {n : ℕ} {p : Velocity × Velocity}
    (hp : p ∈ seedPortion n) {t : ℝ}
    (ht : max 1 (2*(n : ℝ)*((n : ℝ)+1)) ≤ t) :
    t/(2*((n : ℝ)+1)) ≤ ‖transverse (p.1+t • p.2)‖ := by
  have ht0 : 0 ≤ t := (show (0:ℝ) ≤ 1 by norm_num).trans ((le_max_left _ _).trans ht)
  have hl := (seed_flight_bounds hp ht0).1
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hlarge := (le_max_right _ _).trans ht
  have hnle : (n : ℝ) ≤ t/(2*((n : ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have he : t/((n : ℝ)+1) = 2*(t/(2*((n : ℝ)+1))) := by field_simp
  rw [he] at hl
  linarith

theorem seed_flight_outside (n : ℕ) (L : ℝ) : ∃ T : ℝ, 0 < T ∧
    ∀ t, T ≤ t → ∀ p ∈ seedPortion n, L < ‖transverse (p.1+t • p.2)‖ := by
  let T := max (max 1 (2*(n : ℝ)*((n : ℝ)+1))) (2*((n : ℝ)+1)*(|L|+1))
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨T,hT,?_⟩
  intro t ht p hp
  have hl := seed_flight_radius_linear hp ((le_max_left _ _).trans ht)
  have hh : |L|+1 ≤ t/(2*((n : ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by
      have hh := (le_max_right _ _).trans ht
      nlinarith)
  linarith [le_abs_self L]

theorem seed_flight_geometric_scale {n : ℕ} {p : Velocity × Velocity}
    (hp : p ∈ seedPortion n) {t : ℝ}
    (ht : max 1 (2*(n : ℝ)*((n : ℝ)+1)) ≤ t) :
    0 < ‖transverse (p.1+t • p.2)‖ ∧
      t ≤ (4*((n : ℝ)+1)^2)*‖transverse (p.1+t • p.2)‖/2 ∧
      |axial (p.1+t • p.2)| ≤
        (4*((n : ℝ)+1)^2)*‖transverse (p.1+t • p.2)‖/2 := by
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hl := seed_flight_radius_linear hp ht
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnp : 0 < (n : ℝ)+1 := by positivity
  have hmul := (div_le_iff₀ (by positivity : 0 < 2*((n : ℝ)+1))).mp hl
  have hr : 0 < ‖transverse (p.1+t • p.2)‖ := by
    exact (div_pos (by linarith) (by positivity)).trans_le hl
  have hu := (SmallInputGeometry.abs_axial_le_norm _).trans
    ((seed_flight_bounds hp (t := t) (by linarith)).2)
  have htprod : (n : ℝ)*t ≤ ((n : ℝ)+1)*t := by nlinarith
  have hrt := mul_le_mul_of_nonneg_left hmul hnp.le
  refine ⟨hr,?_,?_⟩
  · have htr := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (n : ℝ)+1 by linarith)
      (show 0 ≤ 2*((n : ℝ)+1)*‖transverse (p.1+t • p.2)‖ by positivity)
    nlinarith
  · have hlarge := (le_max_right _ _).trans ht
    have hnt : (n : ℝ) ≤ t := by nlinarith
    nlinarith

end BoltzmannNonuniqueness

end

end

section

/-! # Countably many compact phase cutoffs preserving the positive seed -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def seedPhaseBump (n : ℕ) : ContDiffBump (0 : WeakTime.Phase) :=
  ⟨(n : ℝ)+1,(n : ℝ)+2,by positivity,by linarith⟩

def seedPhaseCutoff (n : ℕ) : WeakTime.Phase → ℝ := seedPhaseBump n

theorem seedPhaseCutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (seedPhaseCutoff n) :=
  (seedPhaseBump n).contDiff

theorem seedPhaseCutoff_compact (n : ℕ) : HasCompactSupport (seedPhaseCutoff n) :=
  (seedPhaseBump n).hasCompactSupport

theorem seedPhaseCutoff_mem (n : ℕ) (p : WeakTime.Phase) :
    seedPhaseCutoff n p ∈ Icc (0:ℝ) 1 :=
  ⟨(seedPhaseBump n).nonneg,(seedPhaseBump n).le_one⟩

theorem seedPhaseCutoff_one {n : ℕ} {p : WeakTime.Phase} (hp : p ∈ seedPortion n) :
    seedPhaseCutoff n p = 1 := by
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
  exact ⟨hp.1.trans (by dsimp [seedPhaseBump]; linarith),
    hp.2.1.trans (by dsimp [seedPhaseBump]; linarith)⟩

theorem phaseSlice_weight_le {F : ℝ × WeakTime.Phase → ℝ} {β : WeakTime.Phase → ℝ}
    (hF : ∀ z, 0 ≤ F z) (hβ : ∀ p, β p ≤ 1) (t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β F) t ≤ WeakTime.phaseSlice F t := by
  apply withDensity_mono
  apply ae_of_all
  intro p
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left (hF _) (hβ p)

theorem phaseSlice_weight_apply_eq {F : ℝ × WeakTime.Phase → ℝ}
    {β : WeakTime.Phase → ℝ} {S : Set WeakTime.Phase} (hS : MeasurableSet S)
    (hβ : ∀ p ∈ S, β p = 1) (t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β F) t S = WeakTime.phaseSlice F t S := by
  unfold WeakTime.phaseSlice positiveDensityMeasure
  rw [withDensity_apply _ hS,withDensity_apply _ hS]
  apply setLIntegral_congr_fun hS
  intro p hp
  change ENNReal.ofReal (β p*F (t,p)) = ENNReal.ofReal (F (t,p))
  rw [hβ p hp,one_mul]

end BoltzmannNonuniqueness

end

end

section

/-! # The surviving seed gives positive physical mass outside any fixed hole -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness

def seedEscapeRegion (n : ℕ) (L t : ℝ) : Set (Velocity × Velocity) :=
  {p | L < ‖transverse p.1‖ ∧ ‖p.1‖ ≤ (n : ℝ)*(1+t) ∧ ‖p.2‖ ≤ n}

theorem seedEscapeRegion_measurable (n : ℕ) (L t : ℝ) :
    MeasurableSet (seedEscapeRegion n L t) := by
  unfold seedEscapeRegion
  measurability

theorem seed_mass_escapes {s : ℝ} {n : ℕ} (μ : ℝ → Measure (Velocity × Velocity))
    (hseed : ∀ᵐ t ∂volume, s ≤ t → 0 < μ t (seedPortion n)) :
    ∀ L : ℝ, ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t →
      0 < (μ t).map (flight t) (seedEscapeRegion n L t) := by
  intro L
  obtain ⟨T₀,hT₀,hout⟩ := seed_flight_outside n L
  let T := max s T₀
  refine ⟨T,hT₀.trans_le (le_max_right _ _),?_⟩
  filter_upwards [hseed] with t ht
  intro hTt
  have hs : s ≤ t := (le_max_left _ _).trans hTt
  have hT : T₀ ≤ t := (le_max_right _ _).trans hTt
  have ht0 : 0 ≤ t := (hT₀.trans_le hT).le
  rw [Measure.map_apply (flight_measurePreserving t).measurable
    (seedEscapeRegion_measurable n L t)]
  apply (ht hs).trans_le
  apply measure_mono
  intro p hp
  exact ⟨hout t hT p hp,(seed_flight_bounds hp ht0).2,hp.2.1⟩

end BoltzmannNonuniqueness

end

end

end OAI
