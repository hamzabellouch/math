import OAI.Analysis.IrrationalRotation.Analysis.TriangularEndpointKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedTriangular

private theorem intervalIntegrable_of_unit_bound {f : ℝ → ℝ}
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    IntervalIntegrable f volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  exact IntegrableOn.of_bound (by simp) hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hbound)

private theorem interval_average_measurable {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) :
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hu.stronglyMeasurable.integral_prod_right.measurable

private theorem norm_le_one_of_bounds {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : ‖x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

theorem dominated_unitKernel_moments {u K : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKbound : ∀ s t, 0 ≤ K s t ∧ K s t ≤ 1)
    (hubound : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t) :
    (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t)) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, u s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t) ^ 2) ≤
      (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, K s t) ^ 2) ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, u s t ^ 2) ≤
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, K s t ^ 2) := by
  have hu01 (s t : ℝ) : 0 ≤ u s t ∧ u s t ≤ 1 :=
    ⟨(hubound s t).1, (hubound s t).2.trans (hKbound s t).2⟩
  have ui (s : ℝ) : IntervalIntegrable (u s) volume 0 1 :=
    intervalIntegrable_of_unit_bound
      (hu.comp (measurable_const.prodMk measurable_id))
      (fun t => norm_le_one_of_bounds (hu01 s t))
  have Ki (s : ℝ) : IntervalIntegrable (K s) volume 0 1 :=
    intervalIntegrable_of_unit_bound
      (hK.comp (measurable_const.prodMk measurable_id))
      (fun t => norm_le_one_of_bounds (hKbound s t))
  have means (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t) := by
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hubound s t).1)
    · exact intervalIntegral.integral_mono zero_le_one (ui s) (Ki s)
        (fun t => (hubound s t).2)
  have Kmean01 (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, K s t) ∧
      (∫ t in (0 : ℝ)..1, K s t) ≤ 1 := by
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hKbound s t).1)
    · calc
        _ ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono zero_le_one (Ki s) intervalIntegrable_const
            (fun t => (hKbound s t).2)
        _ = 1 := by norm_num
  have umean01 (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ 1 :=
    ⟨(means s).1, (means s).2.trans (Kmean01 s).2⟩
  have sq01 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : 0 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 :=
    ⟨sq_nonneg x, pow_le_one₀ hx.1 hx.2⟩
  refine ⟨ui, interval_average_measurable hu, means, fun s => (umean01 s).2, ?_, ?_⟩
  · apply intervalIntegral.integral_mono zero_le_one
      (intervalIntegrable_of_unit_bound ((interval_average_measurable hu).pow_const 2)
        (fun s => norm_le_one_of_bounds (sq01 (umean01 s))))
      (intervalIntegrable_of_unit_bound ((interval_average_measurable hK).pow_const 2)
        (fun s => norm_le_one_of_bounds (sq01 (Kmean01 s))))
    intro s
    exact pow_le_pow_left₀ (means s).1 (means s).2 2
  · have usq (s : ℝ) : IntervalIntegrable (fun t => u s t ^ 2) volume 0 1 :=
      intervalIntegrable_of_unit_bound
        ((hu.comp (measurable_const.prodMk measurable_id)).pow_const 2)
        (fun t => norm_le_one_of_bounds (sq01 (hu01 s t)))
    have Ksq (s : ℝ) : IntervalIntegrable (fun t => K s t ^ 2) volume 0 1 :=
      intervalIntegrable_of_unit_bound
        ((hK.comp (measurable_const.prodMk measurable_id)).pow_const 2)
        (fun t => norm_le_one_of_bounds (sq01 (hKbound s t)))
    have inner01 (v : ℝ → ℝ → ℝ)
        (vi : ∀ s, IntervalIntegrable (fun t => v s t ^ 2) volume 0 1)
        (vb : ∀ s t, 0 ≤ v s t ∧ v s t ≤ 1) (s : ℝ) :
        0 ≤ (∫ t in (0 : ℝ)..1, v s t ^ 2) ∧
          (∫ t in (0 : ℝ)..1, v s t ^ 2) ≤ 1 := by
      constructor
      · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)
      · calc
          _ ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) :=
            intervalIntegral.integral_mono zero_le_one (vi s) intervalIntegrable_const
              (fun t => (sq01 (vb s t)).2)
          _ = 1 := by norm_num
    apply intervalIntegral.integral_mono zero_le_one
      (intervalIntegrable_of_unit_bound (interval_average_measurable (hu.pow_const 2))
        (fun s => norm_le_one_of_bounds (inner01 u usq hu01 s)))
      (intervalIntegrable_of_unit_bound (interval_average_measurable (hK.pow_const 2))
        (fun s => norm_le_one_of_bounds (inner01 K Ksq hKbound s)))
    intro s
    exact intervalIntegral.integral_mono zero_le_one (usq s) (Ksq s)
      (fun t => pow_le_pow_left₀ (hubound s t).1 (hubound s t).2 2)

def firstKernel (E F : Set ℝ) (s t : ℝ) : ℝ :=
  triangularKernel s t * E.indicator (fun _ => 1) s *
    F.indicator (fun _ => 1) (Int.fract (s + t))

theorem triangularKernel_measurable : Measurable (Function.uncurry triangularKernel) := by
  change Measurable (fun p : ℝ × ℝ => triangularKernel p.1 p.2)
  simp only [triangularKernel, Set.indicator_apply, Set.mem_Ioo]
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)))
    measurable_const measurable_const

theorem triangularKernel_bounds (s t : ℝ) :
    0 ≤ triangularKernel s t ∧ triangularKernel s t ≤ 1 := by
  unfold triangularKernel
  by_cases h : t ∈ Ioo 0 (1 - s) <;> simp [h]

theorem firstKernel_measurable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (firstKernel E F)) := by
  exact (triangularKernel_measurable.mul
    ((measurable_const.indicator hE).comp measurable_fst)).mul
    ((measurable_const.indicator hF).comp
      (measurable_fract.comp (measurable_fst.add measurable_snd)))

theorem firstKernel_bounds (E F : Set ℝ) (s t : ℝ) :
    0 ≤ firstKernel E F s t ∧ firstKernel E F s t ≤ triangularKernel s t := by
  have h := triangularKernel_bounds s t
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, h.1]

theorem firstKernel_moment_bounds {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∀ s, IntervalIntegrable (firstKernel E F s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, firstKernel E F s t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      0 ≤ (∫ t in (0 : ℝ)..1, firstKernel E F s t) ∧
        (∫ t in (0 : ℝ)..1, firstKernel E F s t) ≤ 1 - s) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, firstKernel E F s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, firstKernel E F s t) ^ 2) ≤ 1 / 3 ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, firstKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hm, havg, hone, havgsq, hsq⟩ := dominated_unitKernel_moments
    (firstKernel_measurable hE hF) triangularKernel_measurable
    triangularKernel_bounds (firstKernel_bounds E F)
  refine ⟨hi, hm, ?_, hone, ?_, ?_⟩
  · intro s hs
    exact ⟨(havg s).1, (havg s).2.trans_eq (interval_integral_triangularKernel hs)⟩
  · exact havgsq.trans_eq triangularKernel_averaged_secondMoment
  · exact hsq.trans_eq triangularKernel_secondMoment

def secondKernel (E F : Set ℝ) (s t : ℝ) : ℝ :=
  triangularKernel (Int.fract (s - t)) t *
    E.indicator (fun _ => 1) (Int.fract (s - t)) * F.indicator (fun _ => 1) s

theorem endpointKernel_measurable :
    Measurable (fun p : ℝ × ℝ => triangularKernel (Int.fract (p.1 - p.2)) p.2) :=
  triangularKernel_measurable.comp
    ((measurable_fract.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)

theorem secondKernel_measurable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (secondKernel E F)) := by
  exact (endpointKernel_measurable.mul
    ((measurable_const.indicator hE).comp
      (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
    ((measurable_const.indicator hF).comp measurable_fst)

theorem secondKernel_bounds (E F : Set ℝ) (s t : ℝ) :
    0 ≤ secondKernel E F s t ∧
      secondKernel E F s t ≤ triangularKernel (Int.fract (s - t)) t := by
  have h := triangularKernel_bounds (Int.fract (s - t)) t
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, h.1]

theorem secondKernel_moment_bounds {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∀ s, IntervalIntegrable (secondKernel E F s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, secondKernel E F s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, secondKernel E F s t) ∧
      (∫ t in (0 : ℝ)..1, secondKernel E F s t) ≤ Int.fract s) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, secondKernel E F s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, secondKernel E F s t) ^ 2) ≤ 1 / 3 ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, secondKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hm, havg, hone, havgsq, hsq⟩ := dominated_unitKernel_moments
    (K := fun s t => triangularKernel (Int.fract (s - t)) t)
    (secondKernel_measurable hE hF) endpointKernel_measurable
    (fun s t => triangularKernel_bounds (Int.fract (s - t)) t) (secondKernel_bounds E F)
  refine ⟨hi, hm, ?_, hone, ?_, ?_⟩
  · intro s
    exact ⟨(havg s).1,
      (havg s).2.trans_eq (interval_integral_endpoint_triangularKernel_periodic s)⟩
  · exact havgsq.trans_eq endpoint_triangularKernel_averaged_secondMoment
  · exact hsq.trans_eq endpoint_triangularKernel_secondMoment

@[simp] theorem firstKernel_univ_univ (s t : ℝ) :
    firstKernel univ univ s t = triangularKernel s t := by
  simp [firstKernel]

@[simp] theorem secondKernel_univ_univ (s t : ℝ) :
    secondKernel univ univ s t = triangularKernel (Int.fract (s - t)) t := by
  simp [secondKernel]

theorem firstKernel_sq (E F : Set ℝ) (s t : ℝ) :
    firstKernel E F s t ^ 2 = firstKernel E F s t := by
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, triangularKernel_sq]

theorem secondKernel_sq (E F : Set ℝ) (s t : ℝ) :
    secondKernel E F s t ^ 2 = secondKernel E F s t := by
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, triangularKernel_sq]

theorem testedKernel_masses_le {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, firstKernel E F s t) ≤ 1 / 2 ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, secondKernel E F s t) ≤ 1 / 2 := by
  constructor
  · simpa only [firstKernel_sq] using (firstKernel_moment_bounds hE hF).2.2.2.2.2
  · simpa only [secondKernel_sq] using (secondKernel_moment_bounds hE hF).2.2.2.2.2

theorem testedKernel_square_integrable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IntegrableOn (fun p : ℝ × ℝ => firstKernel E F p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) ∧
      IntegrableOn (fun p : ℝ × ℝ => secondKernel E F p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
  constructor
  · apply integrableOn_unitSquare_of_bound
      (F := fun s t => firstKernel E F s t ^ 2) (C := 1)
      ((firstKernel_measurable hE hF).pow_const 2)
    intro s t
    rw [firstKernel_sq, Real.norm_eq_abs, abs_of_nonneg (firstKernel_bounds E F s t).1]
    exact (firstKernel_bounds E F s t).2.trans (triangularKernel_bounds s t).2
  · apply integrableOn_unitSquare_of_bound
      (F := fun s t => secondKernel E F s t ^ 2) (C := 1)
      ((secondKernel_measurable hE hF).pow_const 2)
    intro s t
    rw [secondKernel_sq, Real.norm_eq_abs, abs_of_nonneg (secondKernel_bounds E F s t).1]
    exact (secondKernel_bounds E F s t).2.trans
      (triangularKernel_bounds (Int.fract (s - t)) t).2

theorem testedKernel_reverse_square_moments_le {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, firstKernel E F s t ^ 2) ≤ 1 / 2 ∧
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, secondKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hj⟩ := testedKernel_square_integrable hE hF
  constructor
  · rw [← intervalIntegral_intervalIntegral_swap
      (F := fun s t => firstKernel E F s t ^ 2) hi]
    exact (firstKernel_moment_bounds hE hF).2.2.2.2.2
  · rw [← intervalIntegral_intervalIntegral_swap
      (F := fun s t => secondKernel E F s t ^ 2) hj]
    exact (secondKernel_moment_bounds hE hF).2.2.2.2.2

end Invariant233.ScalarSampling.TestedTriangular

end

end OAI
