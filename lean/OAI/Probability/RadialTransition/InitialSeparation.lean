import OAI.Probability.RadialTransition.PhysicalIteration

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma core_ideal_convex_active {t : ℝ} (ht : 1 ≤ t) (htA : 6912*phaseMass ≤ t) :
    ConvexOn ℝ positiveParameters (onParameters (grandPressure (corePotential t) t)) ∧
    (∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (corePotential t) t) phaseMass β h u) := by
  have hb : ∀ n : ℕ, 0 ≤ (0:ℝ) := fun _ => le_rfl
  have hS : ∀ n : ℕ, 1 ≤ (1:ℝ) := fun _ => le_rfl
  have hs : Summable (fun _ : ℕ => (0:ℝ)) := summable_zero
  have hrow : 2197*t*bumpIntegral⁻¹*(∑' _ : ℕ, (0:ℝ)) ≤ (t^2/8)/8 := by simp; positivity
  have hact := family_ideal_global_active ht phaseMass_pos.le htA hb hS hs hrow
  rw [familyPotential_zero] at hact
  refine ⟨?_, hact⟩
  have ht0 : 0 < t := by linarith
  have hst := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrow
  rw [familyPotential_zero] at hst
  exact convexOn_grandPressure (continuous_corePotential t) (bounded_corePotential t) hst ht0
    (fun r hr => by simpa only [familyPotential_zero] using familyPotential_nonpos_outer hb hS ht (r := r) hr)

lemma initial_separation {τ ε₀ : ℝ} (hτ : 0 < τ) (hε₀ : 0 < ε₀) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ phaseWindow (1/4),
      |onParameters (idealAttraction (grandPressure (corePotential t) t) phaseMass) x-
        onParameters threePlane x| ≤ ε₀ ∧
      HasPhaseGroups (idealAttraction (grandPressure (corePotential t) t) phaseMass) x (τ/2) := by
  obtain ⟨U₀, hU₀, hcut⟩ := uniform_ideal_cutoff (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤3/2) (by norm_num : (0:ℝ)≤2) phaseMass_pos.le
  let U := max U₀ (4*packingDensity)
  have hUU : U₀ ≤ U := le_max_left _ _
  have hU : 1 ≤ U := hU₀.trans hUU
  have hUp : 4*packingDensity ≤ U := le_max_right _ _
  let K := 1+phaseMass/2*(U+4*packingDensity)
  have hK : 0 < K := by have := phaseMass_pos; have := packingDensity_pos; dsimp [K]; positivity
  let η := τ/(4*K)
  have hη : 0 < η := div_pos hτ (by positivity)
  let ε := min ε₀ (min (τ/32) (phaseMass*η^2/16))
  have hε : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by have := phaseMass_pos; positivity))
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have heτ : ε ≤ τ/32 := (min_le_right _ _).trans (min_le_left _ _)
  have heη : ε ≤ phaseMass*η^2/16 := (min_le_right _ _).trans (min_le_right _ _)
  let H := 2+2*phaseMass*U
  have hH : 0 ≤ H := by have := phaseMass_pos; dsimp [H]; positivity
  filter_upwards [corePressure_uniform_bare (by norm_num : (0:ℝ)<1/4) hH hε,
    eventually_ge_atTop (1:ℝ), eventually_ge_atTop (6912*phaseMass)] with t happ ht htA
  let Q := grandPressure (corePotential t) t
  obtain ⟨hQ, hact⟩ := core_ideal_convex_active ht htA
  have hb : ∀ n : ℕ, 0 ≤ (0:ℝ) := fun _ => le_rfl
  have hS : ∀ n : ℕ, 1 ≤ (1:ℝ) := fun _ => le_rfl
  have hs : Summable (fun _ : ℕ => (0:ℝ)) := summable_zero
  have hrow : 2197*t*bumpIntegral⁻¹*(∑' _ : ℕ, (0:ℝ)) ≤ (t^2/8)/8 := by simp; positivity
  have hactive (β h : ℝ) (hβ : β ∈ Icc (1/2:ℝ) (3/2)) (hh : |h| ≤ 2) :
      ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q phaseMass β h u := by
    obtain ⟨κ, hκ, hc, hbound⟩ := hcut t ht htA β hβ h (abs_le.mp hh) phaseMass ⟨phaseMass_pos.le,le_rfl⟩
    have hbound' := hbound.trans (mul_le_mul_of_nonneg_left hUU hκ.le)
    obtain ⟨u, hu, ha⟩ := family_ideal_exists_active ht (by linarith [hβ.1]) phaseMass_pos.le
      hb hS hs hrow hκ hc hU hbound'
    rw [familyPotential_zero] at ha
    exact ⟨u, hu, ha⟩
  have hshift (β h u : ℝ) (hβ : β ∈ Icc (1/2:ℝ) (3/2)) (hh : |h| ≤ 2)
      (hu : u ∈ Icc (0:ℝ) U) : |h+β*phaseMass*u| ≤ H := by
    have hb0 : 0 ≤ β := by linarith [hβ.1]
    have ha0 := phaseMass_pos.le
    have hu0 := hu.1
    have hmul : β*phaseMass*u ≤ 2*phaseMass*U :=
      mul_le_mul (mul_le_mul_of_nonneg_right (show β ≤ 2 by linarith [hβ.2]) phaseMass_pos.le)
        hu.2 hu.1 (by have := phaseMass_pos; positivity)
    calc
      _ ≤ |h|+|β*phaseMass*u| := abs_add_le _ _
      _ ≤ H := by rw [abs_of_nonneg (by positivity : 0 ≤ β*phaseMass*u)]; dsimp [H]; linarith
  intro x hx
  obtain ⟨hβ, hh⟩ := phaseWindow_quarter_bounds hx
  have hβ' : x 0 ∈ Icc (1/2:ℝ) (3/2) := ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hβ0 : 0 < x 0 := by linarith [hβ.1]
  have happx : ∀ u ∈ Icc (0:ℝ) U, |Q (x 0) (x 1+x 0*phaseMass*u)-bareLimit (x 1+x 0*phaseMass*u)| ≤ ε := by
    intro u hu
    exact happ _ _ (by linarith [hβ.1]) (hshift _ _ _ hβ' hh hu)
  constructor
  · obtain ⟨u, hub, hu⟩ := hactive _ _ hβ' hh
    exact (ideal_approx_threePlane hβ0.le hUp hu hub happx).trans he₀
  · have hlocal : ∀ y ∈ Metric.closedBall x (1/16), ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q phaseMass (y 0) (y 1) u := by
      intro y hy
      have hy' : y ∈ phaseWindow (1/2) := phaseWindow_mono (by norm_num : (1/4:ℝ)+1/16≤1/2) (phaseWindow_near hx hy)
      obtain ⟨hyβ, hyh⟩ := phaseWindow_half_bounds hy'
      exact hactive _ _ hyβ hyh
    have hgen := ideal_supportSet_generated hQ phaseMass_pos hact (by norm_num : (0:ℝ)<1/16)
      (by linarith [hβ.1] : 2*(1/16:ℝ)<x 0) hlocal
    apply phase_groups_of_generators hgen
    rintro v ⟨u, hub, hu, e, hes, rfl⟩
    have happe : ∀ s ∈ ({-(1/4:ℝ),0,1/4} : Set ℝ),
        |Q (x 0+s) (x 1+x 0*phaseMass*u)-bareLimit (x 1+x 0*phaseMass*u)| ≤ ε := by
      intro s hs
      have hs' : -(1/4:ℝ) ≤ s := by
        simp only [mem_insert_iff,mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl <;> norm_num
      exact happ _ _ (by linarith [hβ.1]) (hshift _ _ _ hβ' hh hub)
    have hsmall : 2*ε ≤ x 0*phaseMass/2*η^2 := by
      have hm := mul_le_mul_of_nonneg_right hβ.1 (mul_nonneg phaseMass_pos.le (sq_nonneg η))
      nlinarith
    obtain ⟨i, hi⟩ := phase_generator_distance hβ0 (by norm_num : (0:ℝ)<1/4)
      (by linarith [hβ.1]) hη.le hUp hu hub happx happe hsmall hes
    refine ⟨i, Metric.mem_closedBall.mpr ?_⟩
    rw [dist_eq_norm]
    apply hi.trans
    have heq : K*η=τ/4 := by dsimp [η]; field_simp
    change 2*ε/(1/4)+K*η ≤ τ/2
    rw [heq]
    linarith

end RadialTransition
end

end OAI
