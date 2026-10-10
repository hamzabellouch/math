import OAI.Combinatorics.EditApproximation.Geometry.CommonArrayFinal

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

 theorem finite_init_last_law (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => μ).map
      (fun draw => ((fun i : Fin n => draw i.castSucc), draw (Fin.last n))) =
    (Measure.pi fun _ : Fin n => μ).prod μ := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨front, last⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : (fun draw : Fin (n + 1) → Ω =>
      ((fun i : Fin n => draw i.castSucc), draw (Fin.last n))) ⁻¹' {(front, last)} =
      {Fin.snoc front last} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hp, hl⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hl
      · simpa only [Fin.snoc_castSucc] using congrFun hp j
    · rintro rfl
      constructor
      · funext i; simp only [Fin.snoc_castSucc]
      · simp only [Fin.snoc_last]
  rw [hpre, Measure.pi_singleton, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton]

 theorem finite_init_law (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => μ).map
      (fun draw (i : Fin n) => draw i.castSucc) = Measure.pi fun _ : Fin n => μ := by
  have h := congrArg (fun law : Measure ((Fin n → Ω) × Ω) => law.map Prod.fst)
    (finite_init_last_law μ n)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _), Measure.map_fst_prod] at h
  simpa only [Function.comp_def, measure_univ, one_smul] using h

end Law

end EditApproximation

end OAI
