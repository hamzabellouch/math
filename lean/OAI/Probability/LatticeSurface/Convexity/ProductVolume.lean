import Mathlib

namespace OAI

open Set MeasureTheory

universe u v

namespace ProductVolume

variable {ι : Type u} [Fintype ι] {J : ι → Type v} [∀ i, Fintype (J i)]

noncomputable def curry : ((Σ i, J i) → ℝ) ≃ᵐ (∀ i, J i → ℝ) :=
  MeasurableEquiv.piCurry (fun (i : ι) (_ : J i) => ℝ)

lemma curry_volume : MeasurePreserving (curry (J := J)) volume volume := by
  refine MeasurePreserving.symm (curry (J := J)).symm ?_
  refine ⟨(curry (J := J)).symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (curry (J := J)).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (curry (J := J)).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i,j⟩)) := by
    ext x
    simp [curry, Set.mem_pi, Sigma.forall, Sigma.uncurry]
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi]
  exact (Fintype.prod_sigma (fun j : Sigma J => volume (s j))).symm

lemma cond_pi {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (P : ∀ i, Set (X i)) (hP : ∀ i, MeasurableSet (P i))
    (h0 : ∀ i, μ i (P i) ≠ 0) (_hfin : ∀ i, μ i (P i) ≠ ⊤) :
    ProbabilityTheory.cond (Measure.pi μ) (Set.pi Set.univ P) =
      Measure.pi (fun i => ProbabilityTheory.cond (μ i) (P i)) := by
  let : ∀ i, IsProbabilityMeasure (ProbabilityTheory.cond (μ i) (P i)) :=
    fun i => ProbabilityTheory.cond_isProbabilityMeasure_of_finite (h0 i) (_hfin i)
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [ProbabilityTheory.cond_apply (MeasurableSet.univ_pi hP), Measure.pi_pi]
  rw [← Set.pi_inter_distrib, Measure.pi_pi]
  simp_rw [ProbabilityTheory.cond_apply (hP _), Finset.prod_mul_distrib]
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (h0 i))]

lemma preserving_cond {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (P : Set Y) (hP : MeasurableSet P) :
    MeasurePreserving e (ProbabilityTheory.cond μ (e ⁻¹' P))
      (ProbabilityTheory.cond ν P) := by
  refine ⟨e.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply e.measurable ht,
    ProbabilityTheory.cond_apply (hP.preimage e.measurable),
    ProbabilityTheory.cond_apply hP]
  rw [he.measure_preimage hP.nullMeasurableSet, ← Set.preimage_inter, he.measure_preimage (hP.inter ht).nullMeasurableSet]

end ProductVolume

end OAI
