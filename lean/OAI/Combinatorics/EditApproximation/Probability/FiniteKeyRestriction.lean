import Mathlib

namespace OAI

/-! Restricting independent finite key streams preserves their exact
product law. Unused keys need not be allocated by a lazy implementation. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_restrict_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key) :
    (Measure.pi mu).map (fun draw k => draw (key k)) =
      Measure.pi (fun k => mu (key k)) := by
  have hindependent : iIndepFun (fun i (draw : ∀ j, X j) => draw i) (Measure.pi mu) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hrestricted := hindependent.precomp hinjective
  have hmap := hrestricted.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (key k)).aemeasurable)
  simpa only [(measurePreserving_eval mu _).map_eq] using hmap

theorem finite_pi_restrict_image_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : κ → Type*} [∀ k, MeasurableSpace (Y k)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key)
    (image : ∀ k, X (key k) → Y k) (himage : ∀ k, Measurable (image k)) :
    (Measure.pi mu).map (fun draw k => image k (draw (key k))) =
      Measure.pi (fun k => (mu (key k)).map (image k)) := by
  have hrestrict := finite_pi_restrict_map mu key hinjective
  have hproject : Measurable (fun draw : ∀ i, X i => fun k => draw (key k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (key k))
  have htransform : Measurable (fun draw : ∀ k, X (key k) => fun k => image k (draw k)) :=
    Measurable.of_eval (fun k => (himage k).comp (measurable_pi_apply k))
  refine (Measure.map_map htransform hproject).symm.trans ?_
  rw [hrestrict]
  exact Measure.pi_map_pi (fun k => (himage k).aemeasurable)

theorem finite_uniform_array_cast (R n m : ℕ) [NeZero n] [NeZero m] (h : n = m) :
    (Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin n)).toMeasure)).map
      (fun draw t => Fin.cast h (draw t)) =
    Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin m)).toMeasure) := by
  subst m
  simp only [Fin.cast_refl, id_eq, Measure.map_id']

/-- The accepted finite sampler outputs can be keyed by a larger bounded
universe. Restriction and the range equalities give the original independent
time arrays exactly. -/
theorem finite_uniform_arrays_restrict_cast {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ℕ) (n : ι → ℕ) (m : κ → ℕ)
    [∀ i, NeZero (n i)] [∀ k, NeZero (m k)]
    (key : κ → ι) (hinjective : Function.Injective key)
    (hrange : ∀ k, n (key k) = m k) :
    (Measure.pi (fun i => Measure.pi (fun _ : Fin R =>
      (PMF.uniformOfFintype (Fin (n i))).toMeasure))).map
        (fun draw k t => Fin.cast (hrange k) (draw (key k) t)) =
      Measure.pi (fun k => Measure.pi (fun _ : Fin R =>
        (PMF.uniformOfFintype (Fin (m k))).toMeasure)) := by
  have hmap := finite_pi_restrict_image_map
    (fun i => Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin (n i))).toMeasure))
    key hinjective
    (fun k (draw : Fin R → Fin (n (key k))) t => Fin.cast (hrange k) (draw t))
    (fun _ => measurable_of_finite _)
  refine hmap.trans ?_
  congr 1
  funext k
  exact finite_uniform_array_cast R (n (key k)) (m k) (hrange k)

end EditApproximation

end OAI
