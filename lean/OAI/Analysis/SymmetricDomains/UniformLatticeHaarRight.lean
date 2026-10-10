import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash
import OAI.Analysis.SymmetricDomains.TendstoAmbientLocallyUniformly

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Classical

theorem exists_measurable_injective_real (X : Type*) [TopologicalSpace X]
    [MetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    ∃ f : X → ℝ, Measurable f ∧ Function.Injective f := by
  let : MetricSpace X := metrizableSpaceMetric X
  let Y := UniformSpace.Completion X
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  obtain ⟨e,he⟩ := exists_measurableEmbedding_real Y
  exact ⟨fun x => e (x : Y),he.measurable.comp (UniformSpace.Completion.continuous_coe (α := X)).measurable,
    he.injective.comp (UniformSpace.Completion.coe_injective X)⟩

theorem uniform_lattice_measurable_transversal {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    (K : Set G) (hK : IsCompact K)
    (hcover : ∀ g : G, ∃ h : H, ∃ k ∈ K, g=(h:G)*k) :
    ∃ S : Set G, S ⊆ K ∧ MeasurableSet S ∧ ∀ x : G, ∃! h : H, (h:G)*x ∈ S := by
  let : Countable H := countable_of_Lindelof_of_discrete
  obtain ⟨e,hem,hei⟩ := exists_measurable_injective_real G
  let S : Set G := {x | x ∈ K ∧ ∀ h : H, (h:G)*x ∈ K → e x ≤ e ((h:G)*x)}
  refine ⟨S,fun _ hx => hx.1,?_,?_⟩
  · have heq : S=K ∩ ⋂ h : H, {x : G | (h:G)*x ∈ K → e x ≤ e ((h:G)*x)} := by
      ext x; simp only [S,mem_ofPred_eq,mem_inter_iff,mem_iInter]
    rw [heq]
    apply hK.isClosed.measurableSet.inter
    apply MeasurableSet.iInter
    intro h
    exact (hK.isClosed.measurableSet.preimage (continuous_const.mul continuous_id).measurable).imp
      (measurableSet_le hem (hem.comp (continuous_const.mul continuous_id).measurable))
  · intro x
    have hp : IsProperMap (fun h : H => (h:G)*x) :=
      (Homeomorph.mulRight x).isProperMap.comp hH.isProperMap_subtypeVal
    have hf := (hp.isCompact_preimage hK).finite_of_discrete
    have hn : ((fun h : H => (h:G)*x) ⁻¹' K).Nonempty := by
      obtain ⟨h,k,hk,rfl⟩ := hcover x
      exact ⟨h⁻¹,by simpa using hk⟩
    obtain ⟨a,ha,hmin⟩ := Set.exists_min_image _ (fun h : H => e ((h:G)*x)) hf hn
    change (a:G)*x ∈ K at ha
    have has : (a:G)*x ∈ S := by
      refine ⟨ha,?_⟩
      intro h hh
      simpa only [Subgroup.coe_mul,mul_assoc] using hmin (h*a) (by simpa [mul_assoc] using hh)
    refine ⟨a,has,?_⟩
    intro b hb
    apply Subtype.ext
    apply mul_right_cancel (b := x)
    apply hei
    apply le_antisymm
    · have ht := hb.2 (a*b⁻¹) (by simpa only [Subgroup.coe_mul,Subgroup.coe_inv,
        mul_assoc,inv_mul_cancel_left] using ha)
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel_left] using ht
    · exact hmin b hb.1

theorem uniform_lattice_haar_right_invariant {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    (K : Set G) (hK : IsCompact K)
    (hcover : ∀ g : G, ∃ h : H, ∃ k ∈ K, g=(h:G)*k)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  let : Countable H := countable_of_Lindelof_of_discrete
  obtain ⟨S,hSK,hS,hu⟩ := uniform_lattice_measurable_transversal H hH K hK hcover
  have hs : IsFundamentalDomain H S μ := IsFundamentalDomain.mk' hS.nullMeasurableSet hu
  have h0 : μ S ≠ 0 := hs.measure_ne_zero (NeZero.ne μ)
  have htop : μ S ≠ ⊤ := ne_top_of_le_ne_top hK.measure_ne_top (measure_mono hSK)
  constructor
  intro g
  have ht : IsFundamentalDomain H ((fun x : G => x*g) ⁻¹' S) μ := by
    apply IsFundamentalDomain.mk' ((hS.preimage (continuous_mul_const g).measurable).nullMeasurableSet)
    intro x
    change ∃! h : H, (h:G)*x*g ∈ S
    simpa only [mul_assoc] using hu (x*g)
  have heq : (Measure.map (fun x : G => x*g) μ) S=μ S := by
    rw [Measure.map_apply (continuous_mul_const g).measurable hS]
    exact (hs.measure_eq ht).symm
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,Measure.smul_apply] at heq
  have hc : (Measure.modularCharacterFun g : ENNReal)=1 :=
    (ENNReal.mul_eq_right h0 htop).mp heq
  have hc' : Measure.modularCharacterFun g=1 := by exact_mod_cast hc
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,hc',one_smul]

end Release061

end

end OAI
