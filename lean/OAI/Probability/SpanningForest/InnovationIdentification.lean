import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal NNReal

namespace Problem336.InnovationIdentification

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem restrict_map_eq_smul_of_characteristic
    {P : Measure Ω} [IsFiniteMeasure P] {ν : Measure E} [IsFiniteMeasure ν]
    {D : Ω → E} (hD : Measurable D) (A : Set Ω)
    (hchar : ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (D ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun ν θ) :
    (P.restrict A).map D = P A • ν := by
  have : IsFiniteMeasure (P A • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (measure_lt_top P A) (measure_lt_top ν Set.univ)⟩
  apply Measure.ext_of_charFun
  funext θ
  rw [charFun_apply, integral_map hD.aemeasurable (by fun_prop), hchar θ]
  simp only [charFun_apply, integral_smul_measure]

theorem law_and_indep_of_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [IsProbabilityMeasure ν]
    {D : Ω → E} (hD : Measurable D)
    {PastEvent : Set Ω → Prop} (huniv : PastEvent Set.univ)
    (hchar : ∀ A : Set Ω, PastEvent A → ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (D ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun ν θ) :
    P.map D = ν ∧ ∀ {Past : Type*} [MeasurableSpace Past] (Y : Ω → Past),
      (∀ t : Set Past, MeasurableSet t → PastEvent (Y ⁻¹' t)) → IndepFun D Y P := by
  have hLaw : P.map D = ν := by
    simpa using restrict_map_eq_smul_of_characteristic hD Set.univ
      (hchar Set.univ huniv)
  refine ⟨hLaw, ?_⟩
  intro Past _ Y hY
  apply indepFun_iff_measure_inter_preimage_eq_mul.2
  intro s t hs ht
  have heq := congrArg (fun ρ : Measure E => ρ s)
    (restrict_map_eq_smul_of_characteristic hD (Y ⁻¹' t) (hchar _ (hY t ht)))
  rw [Measure.map_apply hD hs, Measure.restrict_apply (hD hs),
    Measure.smul_apply, smul_eq_mul] at heq
  have hLs : ν s = P (D ⁻¹' s) := by
    rw [← hLaw, Measure.map_apply hD hs]
  rw [hLs, mul_comm] at heq
  exact heq

theorem iIndepFun_of_past_characteristic
    {ι : Type*} [LinearOrder ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ι → Measure E} [∀ i, IsProbabilityMeasure (ν i)]
    {D : ι → Ω → E} (hD : ∀ i, Measurable (D i))
    (hchar : ∀ (i : ι) (s : Finset ι) (sets : ι → Set E),
      (∀ j ∈ s, j < i) → (∀ j ∈ s, MeasurableSet (sets j)) → ∀ θ : E,
      (∫ ω in ⋂ j ∈ s, D j ⁻¹' sets j,
        Complex.exp ((inner ℝ (D i ω) θ : ℂ) * Complex.I) ∂P) =
        (P (⋂ j ∈ s, D j ⁻¹' sets j)).toReal • charFun (ν i) θ) :
    iIndepFun D P := by
  classical
  have hLaw (i : ι) : P.map (D i) = ν i := by
    have h := restrict_map_eq_smul_of_characteristic (hD i)
      (⋂ j ∈ (∅ : Finset ι), D j ⁻¹' (Set.univ : Set E))
      (hchar i ∅ (fun _ => Set.univ) (by simp) (by simp))
    simpa using h
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.2
  intro s sets hs
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert i s his ih =>
    have hi : i ∉ s := fun hi => lt_irrefl i (his i hi)
    have hsi : ∀ j ∈ s, MeasurableSet (sets j) :=
      fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hmi : MeasurableSet (sets i) := hs i (Finset.mem_insert_self i s)
    have heq := congrArg (fun ρ : Measure E => ρ (sets i))
      (restrict_map_eq_smul_of_characteristic (hD i)
        (⋂ j ∈ s, D j ⁻¹' sets j) (hchar i s sets his hsi))
    rw [Measure.map_apply (hD i) hmi, Measure.restrict_apply ((hD i) hmi),
      Measure.smul_apply, smul_eq_mul] at heq
    have hLi : ν i (sets i) = P (D i ⁻¹' sets i) := by
      rw [← hLaw i, Measure.map_apply (hD i) hmi]
    rw [hLi, ih hsi, mul_comm] at heq
    simpa only [Finset.set_biInter_insert, Finset.prod_insert hi] using heq

theorem hasLaw_infinitePi_of_past_characteristic
    {ι : Type*} [LinearOrder ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ι → Measure E} [∀ i, IsProbabilityMeasure (ν i)]
    {D : ι → Ω → E} (hD : ∀ i, Measurable (D i))
    (hchar : ∀ (i : ι) (s : Finset ι) (sets : ι → Set E),
      (∀ j ∈ s, j < i) → (∀ j ∈ s, MeasurableSet (sets j)) → ∀ θ : E,
      (∫ ω in ⋂ j ∈ s, D j ⁻¹' sets j,
        Complex.exp ((inner ℝ (D i ω) θ : ℂ) * Complex.I) ∂P) =
        (P (⋂ j ∈ s, D j ⁻¹' sets j)).toReal • charFun (ν i) θ) :
    HasLaw (fun ω i => D i ω) (Measure.infinitePi ν) P := by
  apply (iIndepFun_of_past_characteristic hD hchar).hasLaw_infinitePi
  · intro i
    refine ⟨(hD i).aemeasurable, ?_⟩
    have h := restrict_map_eq_smul_of_characteristic (hD i)
      (⋂ j ∈ (∅ : Finset ι), D j ⁻¹' (Set.univ : Set E))
      (hchar i ∅ (fun _ => Set.univ) (by simp) (by simp))
    simpa using h
  · exact (Measurable.of_eval hD).aemeasurable

theorem hasIndepIncrements_of_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ℝ≥0 → ℝ≥0 → Measure E} [∀ s t, IsProbabilityMeasure (ν s t)]
    {W : ℝ≥0 → Ω → E} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hchar : ∀ (s t : ℝ≥0), s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (ν s t) θ) :
    HasIndepIncrements W P := by
  intro n times htimes
  apply iIndepFun_of_past_characteristic
    (ν := fun i : Fin n => ν (times i.castSucc) (times i.succ))
    (fun i => hW.measurable.sub hW.measurable)
  intro i s sets hprior hsets θ
  apply hchar (times i.castSucc) (times i.succ) (htimes (Fin.castSucc_le_succ i))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  have hjs : j.succ ≤ i.castSucc := by
    exact_mod_cast hprior j hj
  have hjc : j.castSucc ≤ i.castSucc := (Fin.castSucc_le_succ j).trans hjs
  exact ((hW.measurable_le (htimes hjs)).sub
    (hW.measurable_le (htimes hjc))) (hsets j hj)

theorem isPreBrownianReal_of_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hchar : ∀ (s t : ℝ≥0), s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : ℝ,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (gaussianReal 0 (t - s)) θ) :
    IsPreBrownianReal W P := by
  have hinc : HasIndepIncrements W P :=
    hasIndepIncrements_of_past_characteristic hW hchar
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw _ hinc
  intro t
  have hlaw : HasLaw (W t - W 0) (gaussianReal 0 t) P := by
    refine ⟨(hW.measurable.sub hW.measurable).aemeasurable, ?_⟩
    have h := restrict_map_eq_smul_of_characteristic
      (hW.measurable.sub hW.measurable) Set.univ
      (hchar 0 t zero_le Set.univ MeasurableSet.univ)
    simpa using h
  apply hlaw.congr
  filter_upwards [hzero] with ω hω
  simp [hω]

theorem isBrownianReal_of_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (hchar : ∀ (s t : ℝ≥0), s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : ℝ,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (gaussianReal 0 (t - s)) θ) :
    IsBrownianReal W P :=
  ⟨isPreBrownianReal_of_past_characteristic hW hzero hchar, hcont⟩

theorem hasIndepIncrements_of_strict_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ℝ≥0 → ℝ≥0 → Measure E} [∀ s t, IsProbabilityMeasure (ν s t)]
    {W : ℝ≥0 → Ω → E} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hdiag : ∀ s, ν s s = Measure.dirac 0)
    (hchar : ∀ (s t : ℝ≥0), s < t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (ν s t) θ) :
    HasIndepIncrements W P := by
  apply hasIndepIncrements_of_past_characteristic (ν := ν) hW
  intro s t hst A hA θ
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp [hdiag, charFun_apply, measureReal_def]
  · exact hchar s t hst A hA θ

theorem isPreBrownianReal_of_strict_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hchar : ∀ (s t : ℝ≥0), s < t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : ℝ,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (gaussianReal 0 (t - s)) θ) :
    IsPreBrownianReal W P := by
  apply isPreBrownianReal_of_past_characteristic hW hzero
  intro s t hst A hA θ
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp [charFun_apply, measureReal_def]
  · exact hchar s t hst A hA θ

end Problem336.InnovationIdentification

end

end OAI
