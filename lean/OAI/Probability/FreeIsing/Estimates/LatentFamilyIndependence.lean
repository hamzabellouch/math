import OAI.Probability.FreeIsing.Estimates.LatentProductIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_latent_of_fiber_indep
    {ι S A : Type*} {B : ι → Type*}
    [mS : MeasurableSpace S] [MeasurableSpace A]
    [mB : ∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [StandardBorelSpace A]
    (ρ : Measure S) (μ : Measure A)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    (F : ∀ i, S × A → B i) (hF : ∀ i, Measurable (F i))
    (hind : ∀ s, iIndepFun (fun i a => F i (s, a)) μ) :
    iCondIndepFun (mS.comap (Prod.fst : S × A → S)) measurable_fst.comap_le
      F (ρ.prod μ) := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB F hF]
  intro I sets hsets
  let E : ι → Set (S × A) := fun i => F i ⁻¹' sets i
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi => (hsets i hi).preimage (hF i)
  have hEI : MeasurableSet (⋂ i ∈ I, E i) := by
    exact I.measurableSet_biInter hE
  have hcI := condExp_prod_fst ρ μ
    (measurable_const.indicator hEI).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hEI)
  have hc : ∀ i ∈ I,
      (ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
        fun z => ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ := by
    intro i hi
    exact condExp_prod_fst ρ μ
      (measurable_const.indicator (hE i hi)).stronglyMeasurable
      ((integrable_const (1 : ℝ)).indicator (hE i hi))
  have hcall := (Filter.eventually_all_finset I).2 hc
  filter_upwards [hcI, hcall] with z hzI hz
  change ((ρ.prod μ)[(⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzI]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ I,
      ((ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst]) z) =
      ∏ i ∈ I, ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ :=
    Finset.prod_congr rfl hz
  rw [hprod]
  let T : ι → Set A := fun i => (fun a => F i (z.1, a)) ⁻¹' sets i
  have hT : ∀ i ∈ I, MeasurableSet (T i) := by
    intro i hi
    exact (hsets i hi).preimage ((hF i).comp (measurable_const.prodMk measurable_id))
  have hTI : MeasurableSet (⋂ i ∈ I, T i) := I.measurableSet_biInter hT
  have hleft : (fun a => (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) (z.1, a)) =
      (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator, Set.mem_iInter, E, T, Set.mem_preimage]
  rw [hleft]
  have hmass : (∫ a, (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) a ∂μ) =
      μ.real (⋂ i ∈ I, T i) := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hTI)
  rw [hmass]
  have hright : ∀ i ∈ I,
      (∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ) = μ.real (T i) := by
    intro i hi
    change (∫ a, (T i).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) (hT i hi))
  rw [Finset.prod_congr rfl hright]
  unfold Measure.real
  rw [(hind z.1).measure_inter_preimage_eq_mul I hsets, ENNReal.toReal_prod]

theorem iCondIndepFun_latent_infinitePi
    {ι S : Type*} [Countable ι] {A B : ι → Type*}
    [mS : MeasurableSpace S] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [∀ i, StandardBorelSpace (A i)]
    (ρ : Measure S) (ν : ∀ i, Measure (A i))
    [IsFiniteMeasure ρ] [∀ i, IsProbabilityMeasure (ν i)]
    (F : ∀ i, S × A i → B i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun (mS.comap (Prod.fst : S × (∀ i, A i) → S))
      measurable_fst.comap_le
      (fun i z => F i (z.1, z.2 i)) (ρ.prod (Measure.infinitePi ν)) := by
  apply iCondIndepFun_latent_of_fiber_indep ρ (Measure.infinitePi ν)
    (fun i z => F i (z.1, z.2 i))
  · intro i
    exact (hF i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · intro s
    exact iIndepFun_infinitePi (fun i =>
      (hF i).comp (measurable_const.prodMk measurable_id))

end Problem367

end

end OAI
