import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalMixedObservation
import OAI.Analysis.HardSphere.Conditioning.TagPushforward
import OAI.Analysis.HardSphere.Allocation.PhysicalProjectedPrimary
import OAI.Analysis.HardSphere.Conditioning.PrimaryProduct

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

def cellPointReference {K : ℕ} (L : Length) (v : Fin 3→Fin K) : Measure (Torus L) :=
  (cellPathReference v).map (fun e ↦ projectPoint L (e midpointTime))
instance cellPointReference_probability {K : ℕ} (L : Length) (v : Fin 3→Fin K) :
    IsProbabilityMeasure (cellPointReference L v) := by
  unfold cellPointReference
  exact (Measure.isProbabilityMeasure_map_iff (((projectPoint_continuous L).measurable.comp
    (continuous_eval_const midpointTime).measurable).aemeasurable)).mpr inferInstance

def physicalCellPost {N K : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool) :
    Kernel (Torus L×Configuration N L) (Torus L×Torus L×Configuration N L) :=
  (cellExtraKernel (cellPointReference L extra) (centeredCell L (gridCenter L tag)) univ
    (centeredCell_measurable L _)).map (cellObservation b)

theorem physical_branch_observed_reference {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints (N+1) L)) [SFinite μ]
    (g : Fin G) (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (extra tag : Fin 3→Fin K) (b : Bool) :
    taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
      taggedReference
        ((physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
          (physicalPrimaryReference hL g m t r R C S u
            (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
        (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag) =
      ∑i : Fin (N+1), if i∈groupUnion g a then
        ((physicalCellPost (N:=N) L extra tag b) ∘ₖ orderedKernel (uniformBathOrder N) i) ∘ₘ
          (rawPhysicalBranch hL μ g flags a m r R C S s₀ (2*t) u).map
            (fun z ↦ labelBridgePath (N+1) L (2*t) z midpointTime)
        else 0 := by
  classical
  let particle := Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)
  let P := (physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
    (physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) extra)
  change taggedPhysicalBathKernel particle b ∘ₘ taggedReference P (physicalTagEvent particle tag)=_
  rw [taggedReference_comp P _ (physicalTagEvent_measurable particle tag)]
  apply Finset.sum_congr rfl
  intro i _
  have hk : (taggedPhysicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b).comap (Prod.mk i) measurable_prodMk_left=
      (primaryBathKernel b i).comap (physicalFullMidpoint particle) (physicalFullMidpoint_measurable particle) := rfl
  rw [hk]
  have hrange : i∈Set.range particle ↔ i∈groupUnion g a := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.property
    · intro hi; exact ⟨⟨i,hi⟩,rfl⟩
  by_cases hi : i∈groupUnion g a
  · rw [ite_eq_left hi]
    have he : physicalTagEvent (M:=M) (G:=G) (L:=L) particle tag i=(physicalFullMidpoint particle) ⁻¹'
        ((fun F : Option (Fin (N+1))→Torus L ↦ F (some i)) ⁻¹' centeredCell L (gridCenter L tag)) := by
      ext z
      simp only [physicalTagEvent,Set.mem_ofPred_eq,hrange,hi,true_and,Set.mem_preimage]
    rw [he,comp_comap_map,←Measure.restrict_map (physicalFullMidpoint_measurable particle)
      ((centeredCell_measurable L _).preimage (measurable_pi_apply (some i)))]
    change primaryBathKernel b i ∘ₘ (P.map (physicalFullMidpoint particle)).restrict _=_
    dsimp only [P,particle]
    rw [physicalBranch_primary_midpoint hL hK h50 μ g flags a m r R C S s₀ t u extra]
    exact primaryBath_cell_reference _ (cellPointReference L extra) b i _ (centeredCell_measurable L _)
  · rw [ite_eq_right hi]
    have he : physicalTagEvent (M:=M) (G:=G) (L:=L) particle tag i=∅ := by
      ext z; simp [physicalTagEvent,hrange,hi]
    simp [he]

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Ω A G Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G]
lemma sum_allocatedTagLaw_le_ae (μ : Measure Ω) (I : G→Ω→Finset A)
    (hI : ∀g i,MeasurableSet {ω | i∈I g ω}) (κ : A→Kernel Ω Y)
    (hd : ∀ᵐω ∂μ, ∀g g',g≠g' → Disjoint (I g ω) (I g' ω)) :
    ∑g,allocatedTagLaw μ I κ g ≤ ∑i,κ i ∘ₘ μ := by
  classical
  apply Measure.le_iff.2
  intro s hs
  have hbind (i : A) (ν : Measure Ω) : (κ i ∘ₘ ν) s=∫⁻ω,κ i ω s ∂ν :=
    Measure.bind_apply hs (κ i).aemeasurable
  simp only [allocatedTagLaw,Measure.finsetSum_apply,hbind]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simp_rw [←lintegral_indicator (hI _ i)]
  rw [←lintegral_finsetSum _ (fun g _ ↦ ((κ i).measurable_coe hs).indicator (hI g i))]
  apply lintegral_mono_ae
  filter_upwards [hd] with ω hdω
  let T : Finset G := Finset.univ.filter (fun g ↦ i∈I g ω)
  have hT : T.card≤1 := by
    rw [Finset.card_le_one]
    intro g hg g' hg'
    by_contra h
    exact Finset.disjoint_left.mp (hdω g g' h) (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hg').2
  calc
    (∑g,({ω | i∈I g ω}.indicator (fun ω ↦ κ i ω s)) ω)=∑g∈T,κ i ω s := by
      change _=∑g∈Finset.univ.filter (fun g ↦ i∈I g ω),κ i ω s
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    _ ≤ κ i ω s := by
      rw [Finset.sum_const]
      simpa only [one_nsmul] using nsmul_le_nsmul_left (show 0≤κ i ω s from bot_le) hT
end HardSphere.Comparison
namespace HardSphere.Groups
open Sampling Wiener PathCutoff Comparison
attribute [local instance] Classical.propDecidable

lemma groupAt_mem_eligible {N K M G : ℕ} {L : Length}
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L)
    (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (g : Fin G) (v : Fin 3→Fin K) : groupAt g a v⊆eligibleList m r R C S s₀ u v ω := by
  intro i hi
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact allocationPMF_support _ _ _ (ha v) f he _

lemma physical_groups_disjoint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (g h : Fin G) (hgh : g≠h) : Disjoint (groupUnion g a) (groupUnion h a) := by
  apply Finset.disjoint_left.mpr
  intro i hig hih
  obtain ⟨v,_,hiv⟩ := Finset.mem_biUnion.mp hig
  obtain ⟨w,_,hiw⟩ := Finset.mem_biUnion.mp hih
  have hv := groupAt_mem_eligible m r R C S s₀ u ω a ha g v hiv
  have hw := groupAt_mem_eligible m r R C S s₀ u ω a ha h w hiw
  have hvw : v=w := by
    by_contra hn
    exact Finset.disjoint_left.mp (eligibleList_disjoint hL hK m r R C S s₀ u ω hn) hv hw
  rw [←hvw] at hiw
  cases he : a v with
  | none => simp [groupAt,he] at hiv
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hiv hiw
    obtain ⟨k,hk⟩ := hiv
    obtain ⟨l,hl⟩ := hiw
    exact groupPosition_disjoint M G g h hgh k l (f.injective (hk.trans hl.symm))

lemma physicalAllocation_supported_ae {N K : ℕ} {L : Length}
    (m total : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L) :
    ∀ᵐa ∂physicalAllocationKernel (K:=K) m total r R C S s₀ u ω,
      ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) total).support := by
  change ∀ᵐa ∂Measure.pi (fun v ↦ (allocationPMF (eligibleList m r R C S s₀ u v ω) total).toMeasure), _
  apply ae_all_iff.mpr
  intro v
  exact (MeasureTheory.measurePreserving_eval
    (fun w ↦ (allocationPMF (eligibleList m r R C S s₀ u w ω) total).toMeasure) v).quasiMeasurePreserving.tendsto_ae
      (allocation_support_ae _ _)

theorem sum_physical_group_tags_le {N K M G : ℕ} {L : Length}
    {Y : Type*} [MeasurableSpace Y]
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (μ : Measure (ConfigurationPath N L)) [SFinite μ]
    (κ : Fin N→Kernel (ConfigurationPath N L×GridAllocation N K (G*M)) Y) :
    (∑g,allocatedTagLaw (μ.compProd (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) κ g) ≤
      ∑i,κ i ∘ₘ μ.compProd (physicalAllocationKernel m (G*M) r R C S s₀ u) := by
  apply sum_allocatedTagLaw_le_ae
  · intro g i
    exact ((measurable_of_countable (fun a : GridAllocation N K (G*M) ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  · apply Measure.ae_compProd_of_ae_ae
      (((measurable_of_countable (fun a : GridAllocation N K (G*M) ↦
        ∀g h : Fin G,g≠h→Disjoint (groupUnion g a) (groupUnion h a))).comp measurable_snd).setOf)
    filter_upwards [] with ω
    filter_upwards [physicalAllocation_supported_ae m (G*M) r R C S s₀ u ω] with a ha
    exact fun g h hgh ↦ physical_groups_disjoint hL hK m r R C S s₀ u ω a ha g h hgh

end HardSphere.Groups
end
end

end OAI
