import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! # Measurable finite labels along converging measure-preserving maps

This is the local transport step in the profile affinity argument. A common
finite-measure carrier lets continuity of measurable-set preimages control
every label fiber. Relations between two transported labels then pass to the
limit directly, without selecting pointwise values on exceptional sets.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal symmDiff

theorem finiteLabel_disagreement_tendsto
    {X Y I ι : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
    (label : Y → I) (hlabel : Measurable label)
    {l : Filter ι} (φ : ι → C(X, Y)) (φ₀ : C(X, Y))
    (hφ : Tendsto φ l (𝓝 φ₀))
    (hpres : ∀ᶠ n in l, MeasurePreserving (φ n) μ ν)
    (hpres₀ : MeasurePreserving φ₀ μ ν)
    (K : Set X) (Q : Set Y) (hQ : MeasurableSet Q) (hQfin : ν Q ≠ ∞)
    (himage : ∀ᶠ n in l, ∀ x ∈ K, φ n x ∈ Q) :
    Tendsto (fun n => μ {x | x ∈ K ∧ label (φ n x) ≠ label (φ₀ x)}) l (𝓝 0) := by
  classical
  let T : I → Set Y := fun i => Q ∩ label ⁻¹' {i}
  have hT (i : I) : MeasurableSet (T i) := hQ.inter (hlabel (measurableSet_singleton i))
  have hTfin (i : I) : ν (T i) ≠ ∞ :=
    ne_top_of_le_ne_top hQfin (measure_mono inter_subset_left)
  have hlim (i : I) : Tendsto (fun n => μ ((φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i))) l (𝓝 0) :=
    tendsto_measure_symmDiff_preimage_nhds_zero hφ hpres hpres₀ (hT i).nullMeasurableSet (hTfin i)
  have hsum : Tendsto (fun n => ∑ i : I, μ ((φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i))) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [himage] with n hn
  apply (measure_mono (show {x | x ∈ K ∧ label (φ n x) ≠ label (φ₀ x)} ⊆
      ⋃ i ∈ (Finset.univ : Finset I), (φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i) from ?_)).trans
    (measure_biUnion_finset_le _ _)
  rintro x ⟨hx, hneq⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨label (φ n x), Finset.mem_univ _, ?_⟩
  apply Set.mem_symmDiff.mpr
  left
  refine ⟨⟨hn x hx, rfl⟩, ?_⟩
  intro hh
  exact hneq hh.2.symm

/-- Relations between finite transported labels survive the limit because
the exceptional disagreement sets have vanishing measure. -/
theorem relation_of_disagreement_tendsto
    {X I J ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {l : Filter ι} [l.NeBot]
    (f : ι → X → I) (g : ι → X → J) (f₀ : X → I) (g₀ : X → J)
    (R : I → J → Prop)
    (hR : ∀ᶠ n in l, ∀ᵐ x ∂μ, R (f n x) (g n x))
    (hf : Tendsto (fun n => μ {x | f n x ≠ f₀ x}) l (𝓝 0))
    (hg : Tendsto (fun n => μ {x | g n x ≠ g₀ x}) l (𝓝 0)) :
    ∀ᵐ x ∂μ, R (f₀ x) (g₀ x) := by
  have hbound : ∀ᶠ n in l, μ {x | ¬ R (f₀ x) (g₀ x)} ≤
      μ {x | f n x ≠ f₀ x} + μ {x | g n x ≠ g₀ x} := by
    filter_upwards [hR] with n hn
    have hnull : μ {x | ¬ R (f n x) (g n x)} = 0 := ae_iff.mp hn
    have hs : {x | ¬ R (f₀ x) (g₀ x)} ⊆
        ({x | f n x ≠ f₀ x} ∪ {x | g n x ≠ g₀ x}) ∪ {x | ¬ R (f n x) (g n x)} := by
      intro x hx
      by_cases hfx : f n x = f₀ x
      · by_cases hgx : g n x = g₀ x
        · exact Or.inr (by change ¬ R (f n x) (g n x); rwa [hfx, hgx])
        · exact Or.inl (Or.inr hgx)
      · exact Or.inl (Or.inl hfx)
    have hh := (measure_mono (μ := μ) hs).trans (measure_union_le _ _)
    rw [hnull, add_zero] at hh
    exact hh.trans (measure_union_le _ _)
  have hzero : μ {x | ¬ R (f₀ x) (g₀ x)} ≤ 0 :=
    ge_of_tendsto (by simpa only [add_zero] using hf.add hg) hbound
  exact ae_iff.mpr (le_antisymm hzero bot_le)

/-- Local chamber relations pass to the limiting flow maps. The common
carrier is needed only to localize the measurable finite label field. -/
theorem finiteLabel_relation_transport
    {X Y I ι : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
    (label : Y → I) (hlabel : Measurable label)
    {l : Filter ι} [l.NeBot] (φ ψ : ι → C(X, Y)) (φ₀ ψ₀ : C(X, Y))
    (hφ : Tendsto φ l (𝓝 φ₀)) (hψ : Tendsto ψ l (𝓝 ψ₀))
    (hφpres : ∀ᶠ n in l, MeasurePreserving (φ n) μ ν)
    (hψpres : ∀ᶠ n in l, MeasurePreserving (ψ n) μ ν)
    (hφpres₀ : MeasurePreserving φ₀ μ ν) (hψpres₀ : MeasurePreserving ψ₀ μ ν)
    (K : Set X) (Q : Set Y) (hQ : MeasurableSet Q) (hQfin : ν Q ≠ ∞)
    (hφimage : ∀ᶠ n in l, ∀ x ∈ K, φ n x ∈ Q)
    (hψimage : ∀ᶠ n in l, ∀ x ∈ K, ψ n x ∈ Q)
    (R : I → I → Prop)
    (hR : ∀ᶠ n in l, ∀ᵐ x ∂μ.restrict K, R (label (φ n x)) (label (ψ n x))) :
    ∀ᵐ x ∂μ.restrict K, R (label (φ₀ x)) (label (ψ₀ x)) := by
  have hdis (f g : C(X, Y)) :
      μ.restrict K {x | label (f x) ≠ label (g x)} =
        μ {x | x ∈ K ∧ label (f x) ≠ label (g x)} := by
    have hmeas : MeasurableSet {x | label (f x) ≠ label (g x)} :=
      (measurableSet_eq_fun (hlabel.comp f.measurable) (hlabel.comp g.measurable)).compl
    rw [Measure.restrict_apply hmeas]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
  apply relation_of_disagreement_tendsto (μ := μ.restrict K)
    (fun n x => label (φ n x)) (fun n x => label (ψ n x))
    (fun x => label (φ₀ x)) (fun x => label (ψ₀ x)) R hR
  · simpa only [hdis] using finiteLabel_disagreement_tendsto label hlabel φ φ₀
      hφ hφpres hφpres₀ K Q hQ hQfin hφimage
  · simpa only [hdis] using finiteLabel_disagreement_tendsto label hlabel ψ ψ₀
      hψ hψpres hψpres₀ K Q hQ hQfin hψimage

end PolycyclicRecognition

end

end OAI
