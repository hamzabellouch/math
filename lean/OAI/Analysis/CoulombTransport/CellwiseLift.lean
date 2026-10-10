import OAI.Analysis.CoulombTransport.AtomlessTransport
import OAI.Analysis.CoulombTransport.PartitionTransport
import OAI.Analysis.CoulombTransport.CompactPartition
import OAI.Analysis.CoulombTransport.PartitionLabel

namespace OAI

universe uX uY uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.Transport

/-- A finite atomless source admits a lift to any finite law with that source as
marginal, while preserving any prescribed countable measurable label almost everywhere.
This permits cellwise approximation without splitting a three-index mass table. -/
theorem exists_measurable_lift_preserving_label
    {X : Type uX} {Y : Type uY} {ι : Type uIndex} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [Nonempty ι]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f)
    (hmarg : ν.map f = μ) (p : X → ι) (hp : Measurable p) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, p (f (Q x)) = p x := by
  classical
  let B : ι → Set X := fun i => p ⁻¹' {i}
  have hB (i : ι) : MeasurableSet (B i) := hp (measurableSet_singleton i)
  have hdisj : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i, B i) = univ := by
    ext x
    simp [B]
  have htransport (i : ι) : ∃ Q : X → Y, Measurable Q ∧
      (μ.restrict (B i)).map Q = ν.restrict (f ⁻¹' B i) := by
    apply exists_measurable_transport_finite
    simp only [Measure.restrict_apply_univ]
    rw [← hmarg, Measure.map_apply hf (hB i)]
  choose T hT hmap using htransport
  obtain ⟨Q, hQ, hQT, hQmap⟩ := PartitionTransport.exists_map_eq_of_partition
    μ B hB hdisj (by simp [hcover]) T hT
    (fun i => ν.restrict (f ⁻¹' B i)) hmap
  have hsum : Measure.sum (fun i => ν.restrict (f ⁻¹' B i)) = ν := by
    rw [← Measure.restrict_iUnion]
    · simp only [← preimage_iUnion, hcover, preimage_univ, Measure.restrict_univ]
    · intro i j hij
      exact (hdisj hij).preimage f
    · intro i
      exact (hB i).preimage hf
  refine ⟨Q, hQ, hQmap.trans hsum, ?_⟩
  have hlabel (i : ι) : ∀ᵐ x ∂μ.restrict (B i), p (f (T i x)) = i := by
    have hmem : ∀ᵐ x ∂μ.restrict (B i), f (T i x) ∈ B i := by
      apply ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => f y ∈ B i)
        (hT i).aemeasurable
      rw [hmap i]
      exact ae_restrict_mem ((hB i).preimage hf)
    exact hmem
  have hlabel' (i : ι) : ∀ᵐ x ∂μ, x ∈ B i → p (f (T i x)) = i :=
    (ae_restrict_iff' (hB i)).mp (hlabel i)
  have hall : ∀ᵐ x ∂μ, ∀ i, x ∈ B i → p (f (T i x)) = i :=
    ae_all_iff.mpr hlabel'
  filter_upwards [hall] with x hx
  have hxB : x ∈ B (p x) := rfl
  rw [hQT (p x) hxB]
  exact hx (p x) hxB

/-- A lift can preserve the source coordinate to arbitrary precision whenever
that source has compact support. Only the first marginal is approximated; the
entire target law is transported exactly. -/
theorem exists_measurable_lift_close
    {X : Type uX} {Y : Type uY} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f) (hmarg : ν.map f = μ)
    {K : Set X} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, dist x (f (Q x)) < δ := by
  obtain ⟨n, A, hA, hdisj, hcover, _, hdiam⟩ := exists_compact_small_partition hK hδ
  let : MeasurableSpace (Option (Fin n)) := ⊤
  obtain ⟨Q, hQ, hmap, hlabel⟩ := exists_measurable_lift_preserving_label
    μ ν f hf hmarg (FiniteCells.cellLabel A) (FiniteCells.measurable_cellLabel hA hdisj)
  refine ⟨Q, hQ, hmap, ?_⟩
  have hxK : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hfull
  filter_upwards [hlabel, hxK] with x hx hxK
  have hxA : x ∈ ⋃ i, A i := by rwa [hcover]
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
  have hlabelx : FiniteCells.cellLabel A x = some i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj x i).mpr hi
  have hlabelQ : FiniteCells.cellLabel A (f (Q x)) = some i := hx.trans hlabelx
  have hQi : f (Q x) ∈ A i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj (f (Q x)) i).mp hlabelQ
  exact hdiam i x hi (f (Q x)) hQi

end Problem356.Transport

end

end OAI
