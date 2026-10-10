import Mathlib

namespace OAI

section

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace SmoothObstruction

/- The quantile construction gives a measurable map from the unit interval
with the prescribed probability law. Injectivity yields a measurable
isomorphism on conull subsets for nonatomic laws. -/

noncomputable def unitQuantile (μ : Measure I) (t : I) : I :=
  sSup {x | μ.real (Icc 0 x) < t}

lemma monotone_unitQuantile (μ : Measure I) : Monotone (unitQuantile μ) := by
  intro u v huv
  apply sSup_le_sSup
  intro x hx
  exact lt_of_lt_of_le hx (show (u : ℝ) ≤ v from huv)

lemma measurable_unitQuantile (μ : Measure I) : Measurable (unitQuantile μ) :=
  (monotone_unitQuantile μ).measurable

lemma map_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ] :
    volume.map (unitQuantile μ) = μ := by
  apply (volume.map (unitQuantile μ)).ext_of_Iic μ
  intro x
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have μ_in_I : μ.real (Icc 0 x) ∈ I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [Measure.map_apply (measurable_unitQuantile μ) measurableSet_Iic, preimage,
    mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top μ _),
    ← unitInterval.volume_Iic ⟨_, μ_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : unitQuantile μ ξ ≤ x)
    change ξ ≤ μ.real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y ↦ μ.real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf (μ.map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real μ]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      by_contra! h
      simp only [sSup_le_iff, unitQuantile] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ ≤ μ.real (Icc 0 x))
    simp only [sSup_le_iff, unitQuantile]
    intro c hc
    by_contra! h
    have h_lt : ¬ μ.real (Icc 0 x) ≤ μ.real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

lemma strictMono_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : StrictMono (unitQuantile μ) := by
  intro u v huv
  refine lt_of_le_of_ne (monotone_unitQuantile μ huv.le) ?_
  intro heq
  have hnull : (volume : Measure I) ((unitQuantile μ) ⁻¹' {unitQuantile μ u}) = 0 := by
    rw [← Measure.map_apply (measurable_unitQuantile μ) (measurableSet_singleton _),
      map_unitQuantile, measure_singleton]
  have hsub : Icc u v ⊆ (unitQuantile μ) ⁻¹' {unitQuantile μ u} := by
    intro t ht
    exact le_antisymm ((monotone_unitQuantile μ ht.2).trans_eq heq.symm)
      (monotone_unitQuantile μ ht.1)
  have hzero := measure_mono_null hsub hnull
  rw [unitInterval.volume_Icc, ENNReal.ofReal_eq_zero] at hzero
  exact not_le_of_gt (sub_pos.mpr (show (u : ℝ) < v from huv)) hzero

lemma embedding_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : MeasurableEmbedding (unitQuantile μ) :=
  (measurable_unitQuantile μ).measurableEmbedding (strictMono_unitQuantile μ).injective


/-- Measure-space isomorphism after removing measurable null sets. -/
def ConullIsomorphic {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y))

/-- Standard nonatomic in the source's explicit modulo-null-set sense. -/
def StandardNonatomic {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ConullIsomorphic μ
    (volume.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))

lemma equivImage_preserving {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (hf : MeasurableEmbedding f) (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving (hf.equivImage A) (μ.comap (Subtype.val : A → X))
      ((μ.map f).comap (Subtype.val : f '' A → Z)) := by
  refine ⟨(hf.equivImage A).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe (hf.measurableSet_image' hA)).map_injective
  rw [Measure.map_map measurable_subtype_coe (hf.equivImage A).measurable,
    map_comap_subtype_coe (hf.measurableSet_image' hA)]
  change (μ.comap (Subtype.val : A → X)).map (f ∘ Subtype.val) = _
  rw [← Measure.map_map hf.measurable measurable_subtype_coe,
    map_comap_subtype_coe hA, hf.restrict_map, hf.injective.preimage_image]

private def setEqEquiv {Z : Type*} [MeasurableSpace Z] {A B : Set Z} (h : A = B) :
    A ≃ᵐ B := by
  subst B
  exact MeasurableEquiv.refl A

private lemma setEqEquiv_preserving {Z : Type*} [MeasurableSpace Z] {A B : Set Z}
    (h : A = B) (μ : Measure Z) :
    MeasurePreserving (setEqEquiv h) (μ.comap (Subtype.val : A → Z))
      (μ.comap (Subtype.val : B → Z)) := by
  subst B
  exact MeasurePreserving.id _

/-- Two measurable embeddings having the same image law give an actual
measurable isomorphism on conull sets, not merely two factors. -/
lemma conullIsomorphic_of_common_embedding {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Z} {g : Y → Z} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure X) (ν : Measure Y) (heq : μ.map f = ν.map g) :
    ConullIsomorphic μ ν := by
  let A := f ⁻¹' range g
  let B := g ⁻¹' range f
  have hA : MeasurableSet A := hf.measurable hg.measurableSet_range
  have hB : MeasurableSet B := hg.measurable hf.measurableSet_range
  have hAnull : μ Aᶜ = 0 := by
    change μ (f ⁻¹' (range g)ᶜ) = 0
    rw [← hf.map_apply, heq, hg.map_apply]
    simp
  have hBnull : ν Bᶜ = 0 := by
    change ν (g ⁻¹' (range f)ᶜ) = 0
    rw [← hg.map_apply, ← heq, hf.map_apply]
    simp
  have hAB : f '' A = g '' B := by
    simp only [A, B, image_preimage_eq_inter_range, inter_comm]
  let eA := hf.equivImage A
  let eB := hg.equivImage B
  let eC := setEqEquiv hAB
  have hC : MeasurePreserving eC ((μ.map f).comap (Subtype.val : f '' A → Z))
      ((ν.map g).comap (Subtype.val : g '' B → Z)) := by
    rw [heq]
    exact setEqEquiv_preserving hAB _
  refine ⟨A, B, hA, hB, hAnull, hBnull, eA.trans (eC.trans eB.symm), ?_⟩
  exact (MeasurePreserving.symm eB (equivImage_preserving hg ν hB)).comp
    (hC.comp (equivImage_preserving hf μ hA))

lemma nullSingleton_map_embedding {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : MeasurableEmbedding f)
    (μ : Measure X) [NullSingletonClass μ] : NullSingletonClass (μ.map f) := by
  constructor
  intro y
  rw [hf.map_apply]
  exact (Set.subsingleton_singleton.preimage hf.injective).measure_zero μ

/-- The nonatomic standard-Borel classification needed by prop:system,
with the same closed-unit-interval reference as the frozen main target. -/
theorem standardNonatomic_of_standardBorel {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : StandardNonatomic μ := by
  let f := sigmoid ∘ embeddingReal X
  have hf : MeasurableEmbedding f := measurableEmbedding_sigmoid_comp_embeddingReal X
  let ρ := μ.map f
  have : IsProbabilityMeasure ρ := inferInstance
  have : NullSingletonClass ρ := nullSingleton_map_embedding hf μ
  have hq := embedding_unitQuantile ρ
  have h := conullIsomorphic_of_common_embedding hf hq μ volume (map_unitQuantile ρ).symm
  exact h

end SmoothObstruction

end

end OAI
