import OAI.Probability.RadialTransition.WindowLipschitz

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def AdmissibleFamily (_t A : ℝ) (b S : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ b n) ∧ (∀ n, 1 ≤ S n) ∧ Summable b ∧ ∑' n, b n ≤ A

lemma admissible_row {t A : ℝ} {b S : ℕ → ℝ}
    (ht : 0 ≤ t) (had : AdmissibleFamily t A b S)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8 :=
  (mul_le_mul_of_nonneg_left had.2.2.2 (by have := bumpIntegral_pos; positivity)).trans hrow

lemma admissible_pressure_convex {t A : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (had : AdmissibleFamily t A b S)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    ConvexOn ℝ positiveParameters (onParameters (grandPressure (familyPotential t b S) t)) := by
  have ht0 : 0 < t := by linarith
  have hr := admissible_row ht0.le had hrow
  exact convexOn_grandPressure (continuous_familyPotential had.1 had.2.1 had.2.2.1 t)
    (bounded_familyPotential had.1 had.2.1 had.2.2.1 t)
    (stable_family_of_master ht0.le had.1 had.2.1 had.2.2.1 had.2.2.1 (fun _ => le_rfl) hr) ht0
    (fun r h => familyPotential_nonpos_outer had.1 had.2.1 ht h)

lemma family_controls {t A : ℝ} (ht : 1 ≤ t) (hA : 0 ≤ A) (htA : 6912*A ≤ t)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    ∃ U C C₀ : ℝ, 1 ≤ U ∧ 1 ≤ C ∧ 0 < C₀ ∧
      ∀ b S : ℕ → ℝ, AdmissibleFamily t A b S → ∀ a ∈ Ioc (0:ℝ) A,
      (∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (familyPotential t b S) t) a β h u) ∧
      (∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U,
        ActiveShift (grandPressure (familyPotential t b S) t) a (x 0) (x 1) u) ∧
      (∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
        |onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) y| ≤ C*dist x y) ∧
      (∀ x ∈ phaseWindow (1/4),
        0 ≤ onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ∧
        onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ≤ C₀*a) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨U,hU,hcut⟩ := uniform_ideal_cutoff (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1/4:ℝ)≤2) (by norm_num : (0:ℝ)≤4) hA
  let M := Real.exp (t^2+t*(4+2*A*U))/t
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨U,1+8*M,1+U^2,hU,by linarith,by positivity,?_⟩
  intro b S had a ha
  have hr := admissible_row ht0.le had hrow
  have hta : 6912*a ≤ t := (mul_le_mul_of_nonneg_left ha.2 (by norm_num)).trans htA
  have hQ := admissible_pressure_convex ht had hrow
  have hact := family_ideal_global_active ht ha.1.le hta had.1 had.2.1 had.2.2.1 hr
  have hP := convexOn_idealAttraction hQ hact
  have hcut' (x : Parameter) (hx : x ∈ phaseWindow (1/2)) :
      ∃ u ∈ Icc (0:ℝ) U, ActiveShift (grandPressure (familyPotential t b S) t) a (x 0) (x 1) u := by
    obtain ⟨hβ,hh⟩ := phaseWindow_half_bounds hx
    obtain ⟨κ,hκ,hc,hbound⟩ := hcut t ht htA (x 0) ⟨by linarith [hβ.1],by linarith [hβ.2]⟩
      (x 1) (by have := abs_le.mp hh; constructor <;> linarith) a ⟨ha.1.le,ha.2⟩
    exact family_ideal_exists_active ht (by linarith [hβ.1]) ha.1.le had.1 had.2.1 had.2.2.1 hr hκ hc hU hbound
  have hbound (x : Parameter) (hx : x ∈ phaseWindow (1/2)) :
      |onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x| ≤ M := by
    obtain ⟨hβ,hh⟩ := phaseWindow_half_bounds hx
    have hβ0 : 0 < x 0 := by linarith [hβ.1]
    obtain ⟨u,hub,hu⟩ := hcut' x hx
    have hs := stable_family_of_master ht0.le had.1 had.2.1 had.2.2.1 had.2.2.1 (fun _ => le_rfl) hr
    have hφ := continuous_familyPotential had.1 had.2.1 had.2.2.1 t
    have hbd := bounded_familyPotential had.1 had.2.1 had.2.2.1 t
    have hn := (grandPressure_spec hφ hbd hs ht0 hβ0.le
      (fun r h => familyPotential_nonpos_outer had.1 had.2.1 ht h) (x 1)).2.1
    have hP0 := ideal_nonneg_of_active hu hn
    change |idealAttraction (grandPressure (familyPotential t b S) t) a (x 0) (x 1)| ≤ M
    rw [abs_of_nonneg hP0,idealAttraction_eq_of_active hu]
    have hp := (grandPressure_spec hφ hbd hs ht0 hβ0.le
      (fun r h => familyPotential_nonpos_outer had.1 had.2.1 ht h) (x 1+x 0*a*u)).2.2
    have hmul : x 0*a*u ≤ 2*A*U :=
      mul_le_mul (mul_le_mul (show x 0≤2 by linarith [hβ.2]) ha.2 ha.1.le (by norm_num))
        hub.2 hub.1 (by positivity)
    have hexp : x 0*(t^2/2)+t*(x 1+x 0*a*u) ≤ t^2+t*(4+2*A*U) := by
      have hh' := (abs_le.mp hh).2
      have hbmul := mul_le_mul_of_nonneg_right (show x 0≤2 by linarith [hβ.2]) (sq_nonneg t)
      have hhmul := mul_le_mul_of_nonneg_left hh' ht0.le
      nlinarith [mul_le_mul_of_nonneg_left hmul ht0.le]
    have hd := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) ht0.le
    dsimp [attractionBranch,M]
    have ha0 := ha.1.le
    have hsub : 0 ≤ x 0*a/2*u^2 := by positivity
    linarith
  refine ⟨hact,hcut',?_,?_⟩
  · intro x hx y hy
    exact (window_lipschitz hM.le hP hbound x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith : 8*M≤1+8*M) dist_nonneg)
  · intro x hx
    obtain ⟨u,hub,hu⟩ := hcut' x (phaseWindow_mono (by norm_num) hx)
    have hβ := (phaseWindow_quarter_bounds hx).1
    have hh := ideal_increment_bound hQ ha.1 (by linarith [hβ.1]) hu hub
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hm := mul_le_mul_of_nonneg_right (show x 0≤2 by linarith [hβ.2]) (mul_nonneg ha.1.le (sq_nonneg U))
    nlinarith [ha.1]

end RadialTransition
end

end OAI
