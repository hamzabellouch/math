import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.CompactControls

namespace OAI

open Set MeasureTheory

namespace CompactCoupling

variable {X Y U : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [CompactSpace Y] [SecondCountableTopology Y]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [T2Space U] [CompactSpace U] [SecondCountableTopology U]

noncomputable def family (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Set (ProbabilityMeasure (X×Y)) :=
  {π | π.map Prod.fst=μ ∧ π.map Prod.snd=ν}

lemma compact_family (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : IsCompact (family μ ν) := by
  exact ((isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)).isCompact

omit [TopologicalSpace X] [BorelSpace X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [BorelSpace Y] [T2Space Y] [CompactSpace Y] in
lemma nonempty_family (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : (family μ ν).Nonempty := by
  refine ⟨⟨(μ:Measure X).prod (ν:Measure Y),inferInstance⟩,?_,?_⟩
  · apply Subtype.ext
    change Measure.map Prod.fst ((μ:Measure X).prod (ν:Measure Y))=(μ:Measure X)
    simp
  · apply Subtype.ext
    change Measure.map Prod.snd ((μ:Measure X).prod (ν:Measure Y))=(ν:Measure Y)
    simp

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y]
  [T2Space U] [CompactSpace U] in
lemma step_stays (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (ρ : Measure U) [IsProbabilityMeasure ρ]
    (T : X×U → X) (S : Y×U → Y) (hT : Continuous T) (hS : Continuous S)
    (hμ : Measure.map T ((μ:Measure X).prod ρ)=μ)
    (hν : Measure.map S ((ν:Measure Y).prod ρ)=ν)
    (π : ProbabilityMeasure (X×Y)) (hπ : π∈family μ ν) :
    CompactControls.step ρ (fun z : (X×Y)×U => (T (z.1.1,z.2),S (z.1.2,z.2)))
      ((hT.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
        (hS.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))) π∈family μ ν := by
  have hp : Measure.map Prod.fst (π:Measure (X×Y))=μ := congrArg Subtype.val hπ.1
  have hq : Measure.map Prod.snd (π:Measure (X×Y))=ν := congrArg Subtype.val hπ.2
  have hs : Measurable (fun z : (X×Y)×U => (T (z.1.1,z.2),S (z.1.2,z.2))) := ((hT.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
        (hS.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).measurable
  constructor
  · apply Subtype.ext
    change Measure.map Prod.fst (Measure.map _ ((π:Measure (X×Y)).prod ρ))=(μ:Measure X)
    rw [Measure.map_map measurable_fst hs]
    change Measure.map (T ∘ Prod.map Prod.fst id) ((π:Measure (X×Y)).prod ρ)=(μ:Measure X)
    rw [← Measure.map_map hT.measurable (measurable_fst.prodMap measurable_id),
      ← Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id,hp]
    exact hμ
  · apply Subtype.ext
    change Measure.map Prod.snd (Measure.map _ ((π:Measure (X×Y)).prod ρ))=(ν:Measure Y)
    rw [Measure.map_map measurable_snd hs]
    change Measure.map (S ∘ Prod.map Prod.snd id) ((π:Measure (X×Y)).prod ρ)=(ν:Measure Y)
    rw [← Measure.map_map hS.measurable (measurable_snd.prodMap measurable_id),
      ← Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id,hq]
    exact hν

omit [T2Space U] in
theorem exists_zero {I : Type*} (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (ρ : Measure U) [IsProbabilityMeasure ρ] (hρ : ∀ u,u∈ρ.support) (u₀ : U)
    (T : I → X×U → X) (S : I → Y×U → Y) (hT : ∀ i,Continuous (T i)) (hS : ∀ i,Continuous (S i))
    (hμ : ∀ i,Measure.map (T i) ((μ:Measure X).prod ρ)=μ)
    (hν : ∀ i,Measure.map (S i) ((ν:Measure Y).prod ρ)=ν)
    (d H : X×Y → ℝ) (hd : Continuous d) (hH : Continuous H)
    (hdec : ∀ i z u,d (T i (z.1,u),S i (z.2,u))≤d z)
    (hdown : ∀ i z,H (T i (z.1,u₀),S i (z.2,u₀))≤H z)
    (hfixed : ∀ z,(∀ i,H (T i (z.1,u₀),S i (z.2,u₀))=H z) → d z=0) :
    ∃ π : ProbabilityMeasure (X×Y),π∈family μ ν ∧ ∀ᵐ z∂(π:Measure (X×Y)),d z=0 := by
  exact CompactControls.exists_zero ρ hρ u₀
    (fun i z => (T i (z.1.1,z.2),S i (z.1.2,z.2)))
    (fun i => ((hT i).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
      ((hS i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    (family μ ν) (compact_family μ ν) (nonempty_family μ ν)
    (fun π hπ i => step_stays μ ν ρ (T i) (S i) (hT i) (hS i) (hμ i) (hν i) π hπ)
    d H hd hH hdec hdown hfixed

end CompactCoupling

end OAI
