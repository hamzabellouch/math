import OAI.Analysis.IrrationalRotation.Analysis.TestedTriangularMoments
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelEstimates

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedSampling

theorem dominated_boundedKernel_moments {u K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKb : ∀ s t, 0 ≤ K s t ∧ K s t ≤ C)
    (hub : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t) :
    (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t)) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t) ^ 2) ≤
      (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, K s t) ^ 2) ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, u s t ^ 2) ≤
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, K s t ^ 2) := by
  have hbK (s t : ℝ) : 0 ≤ K s t / C ∧ K s t / C ≤ 1 :=
    ⟨div_nonneg (hKb s t).1 hC.le, (div_le_one hC).2 (hKb s t).2⟩
  have hbu (s t : ℝ) : 0 ≤ u s t / C ∧ u s t / C ≤ K s t / C :=
    ⟨div_nonneg (hub s t).1 hC.le, div_le_div_of_nonneg_right (hub s t).2 hC.le⟩
  obtain ⟨hi, _, hm, _, ha, hb⟩ := TestedTriangular.dominated_unitKernel_moments
    (u := fun s t => u s t / C) (K := fun s t => K s t / C)
    (hu.div_const C) (hK.div_const C) hbK hbu
  refine ⟨?_, measurable_interval_average hu, ?_, ?_, ?_⟩
  · intro s
    convert (hi s).mul_const C using 1; simp [hC.ne']
  · intro s
    have hs := hm s
    simp only [intervalIntegral.integral_div] at hs
    exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hub s t).1),
      (div_le_div_iff_of_pos_right hC).1 hs.2⟩
  · simp only [intervalIntegral.integral_div, div_pow] at ha
    exact (div_le_div_iff_of_pos_right (pow_pos hC 2)).1 ha
  · simp only [div_pow, intervalIntegral.integral_div] at hb
    exact (div_le_div_iff_of_pos_right (pow_pos hC 2)).1 hb

def firstKernel (m : ℕ) (E F : Set ℝ) (s t : ℝ) : ℝ :=
  manuscriptKernel m s t * E.indicator (fun _ => 1) s *
    F.indicator (fun _ => 1) (Int.fract (s + t))

def secondKernel (m : ℕ) (E F : Set ℝ) (s t : ℝ) : ℝ :=
  manuscriptEndpointKernel m s t *
    E.indicator (fun _ => 1) (Int.fract (s - t)) * F.indicator (fun _ => 1) s

private theorem first_measurable (m : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (firstKernel m E F)) :=
  ((measurable_circleKernel _ _).mul
    ((measurable_const.indicator hE).comp measurable_fst)).mul
    ((measurable_const.indicator hF).comp
      (measurable_fract.comp (measurable_fst.add measurable_snd)))

private theorem second_measurable (m : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (secondKernel m E F)) :=
  ((measurable_circleEndpoint_pair _ _).mul
    ((measurable_const.indicator hE).comp
      (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
    ((measurable_const.indicator hF).comp measurable_fst)

def MomentBounds (m : ℕ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
  Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
  (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧ (∫ t in (0 : ℝ)..1, u s t) ≤ 2) ∧
  (0 ≤ (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t)^2) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2) ∧
  (0 ≤ (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, u s t^2) ∧
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, u s t^2) ≤
      (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2))

private theorem momentBounds_of_domination {m : ℕ} {u K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKb : ∀ s t, 0 ≤ K s t ∧ K s t ≤ C)
    (hub : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t)
    (hest : KernelEstimates m K) : MomentBounds m u := by
  obtain ⟨hi, hm, hmean, havg, hsq⟩ := dominated_boundedKernel_moments hC hu hK hKb hub
  refine ⟨hi, hm, ?_, ?_, ?_⟩
  · intro s
    exact ⟨(hmean s).1, (hmean s).2.trans (hest.average_bounds s).2⟩
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _),
      havg.trans hest.average_square_upper⟩
  · have hsquare : IntegrableOn (fun p : ℝ × ℝ => u p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
      apply integrableOn_unitSquare_of_bound (F := fun s t => u s t ^ 2)
        (C := C ^ 2) (hu.pow_const 2)
      intro s t
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hub s t).1]
      exact pow_le_pow_left₀ (hub s t).1 ((hub s t).2.trans (hKb s t).2) 2
    constructor
    · apply intervalIntegral.integral_nonneg_of_forall zero_le_one
      intro t
      exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)
    · rw [← intervalIntegral_intervalIntegral_swap (F := fun s t => u s t ^ 2) hsquare]
      exact hsq.trans_eq hest.square_mass

theorem firstKernel_moment_bounds {m : ℕ} (hm : 200 ≤ m) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (firstKernel m E F) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hb (s t : ℝ) : 0 ≤ manuscriptKernel m s t ∧
      manuscriptKernel m s t ≤
        ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ :=
    rawKernel_height hh hα
  apply momentBounds_of_domination (K := manuscriptKernel m)
    (inv_pos.mpr (mul_pos hh hα))
    (first_measurable m hE hF) (measurable_circleKernel _ _) hb
    (hest := manuscriptKernel_estimates hm)
  intro s t
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, (hb s t).1]

theorem secondKernel_moment_bounds {m : ℕ} (hm : 200 ≤ m) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (secondKernel m E F) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hb (s t : ℝ) : 0 ≤ manuscriptEndpointKernel m s t ∧
      manuscriptEndpointKernel m s t ≤
        ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ :=
    rawKernel_height hh hα
  apply momentBounds_of_domination (K := manuscriptEndpointKernel m)
    (inv_pos.mpr (mul_pos hh hα))
    (second_measurable m hE hF) (measurable_circleEndpoint_pair _ _) hb
    (hest := manuscriptEndpointKernel_estimates hm)
  intro s t
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, (hb s t).1]

@[simp] theorem firstKernel_univ_univ (m : ℕ) (s t : ℝ) :
    firstKernel m univ univ s t = manuscriptKernel m s t := by simp [firstKernel]

@[simp] theorem secondKernel_univ_univ (m : ℕ) (s t : ℝ) :
    secondKernel m univ univ s t = manuscriptEndpointKernel m s t := by simp [secondKernel]

theorem secondKernel_eq_literal (m : ℕ) (E F : Set ℝ) (s t : ℝ) :
    secondKernel m E F s t = manuscriptKernel m (Int.fract (s - t)) t *
      E.indicator (fun _ => 1) (Int.fract (s - t)) * F.indicator (fun _ => 1) s := by
  simp [secondKernel, manuscriptEndpointKernel, manuscriptKernel, circleKernel]

end Invariant233.ScalarSampling.TestedSampling

end

end OAI
