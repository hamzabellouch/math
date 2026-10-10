import Mathlib
import OAI.Analysis.HardSphere.Kernels.FiniteKernelPi
import OAI.Analysis.HardSphere.Allocation.WeightedExpose

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

abbrev GridAllocation (N K q : ℕ) := (Fin 3→Fin K)→Allocation q (Fin N)

def gridAllocationKernel {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ) :
    Kernel (BridgeEndpoints N L×(Fin N→Bool)) (GridAllocation N K q) :=
  finiteKernelPi (fun v : Fin 3→Fin K ↦ (allocationKernel q).comap (recordedList hL v) (recordedList_measurable hL v))

lemma gridAllocationKernel_apply {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ)
    (p : BridgeEndpoints N L×(Fin N→Bool)) :
    gridAllocationKernel hL q p=Measure.pi (fun v ↦ (allocationPMF (recordedList hL v p) q).toMeasure) := by
  rw [gridAllocationKernel,finiteKernelPi_apply]
  rfl

instance gridAllocationKernel_markov {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ) :
    IsMarkovKernel (gridAllocationKernel (N:=N) hL q) := by
  constructor
  intro p
  rw [gridAllocationKernel_apply]
  infer_instance

def groupPosition (M G : ℕ) (g : Fin G) : Fin M↪Fin (G*M) where
  toFun k := ⟨g.val*M+k.val, by
    have hg : g.val+1≤G := g.isLt
    have hk := k.isLt
    calc
      g.val*M+k.val < g.val*M+M := Nat.add_lt_add_left hk _
      _ = (g.val+1)*M := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ G*M := Nat.mul_le_mul_right M hg⟩
  inj' := by intros a b h; apply Fin.ext; have he := congrArg Fin.val h; dsimp at he; omega

lemma groupPosition_disjoint (M G : ℕ) (g h : Fin G) (hgh : g≠h) (k l : Fin M) :
    groupPosition M G g k≠groupPosition M G h l := by
  intro he
  have he' := congrArg Fin.val he
  change g.val*M+k.val=h.val*M+l.val at he'
  wlog hlt : g.val<h.val generalizing g h k l
  · have hne : g.val≠h.val := fun h ↦ hgh (Fin.ext h)
    exact this h g hgh.symm l k he.symm he'.symm (by omega)
  have hh : (g.val+1)*M≤h.val*M := Nat.mul_le_mul_right M hlt
  have hk := k.isLt
  have : g.val*M+k.val<h.val*M+l.val := by
    calc
      g.val*M+k.val < g.val*M+M := Nat.add_lt_add_left hk _
      _ = (g.val+1)*M := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ h.val*M := hh
      _ ≤ h.val*M+l.val := Nat.le_add_right _ _
  omega

def groupAt {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) : Finset (Fin N) :=
  match a v with
  | none => ∅
  | some f => Finset.univ.image (fun k ↦ f (groupPosition M G g k))

def groupUnion {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) : Finset (Fin N) :=
  Finset.univ.biUnion (groupAt g a)

lemma groupAt_mem_list {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (recordedList hL v p) (G*M)).support)
    (g : Fin G) (v : Fin 3→Fin K) : groupAt g a v⊆recordedList hL v p := by
  intro i hi
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact allocationPMF_support _ _ _ (ha v) f he _

lemma groups_disjoint {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (recordedList hL v p) (G*M)).support)
    (g h : Fin G) (hgh : g≠h) : Disjoint (groupUnion g a) (groupUnion h a) := by
  apply Finset.disjoint_left.mpr
  intro i hig hih
  obtain ⟨v,_,hiv⟩ := Finset.mem_biUnion.mp hig
  obtain ⟨w,_,hiw⟩ := Finset.mem_biUnion.mp hih
  have hv := (Finset.mem_filter.mp (groupAt_mem_list hL p a ha g v hiv)).2.1
  have hw := (Finset.mem_filter.mp (groupAt_mem_list hL p a ha h w hiw)).2.1
  have hvw : v=w := hv.symm.trans hw
  rw [←hvw] at hiw
  cases he : a v with
  | none => simp [groupAt,he] at hiv
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hiv hiw
    obtain ⟨k,hk⟩ := hiv
    obtain ⟨l,hl⟩ := hiw
    exact groupPosition_disjoint M G g h hgh k l (f.injective (hk.trans hl.symm))

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma allocation_support_ae {I : Type*} [Fintype I] [DecidableEq I]
    (E : Finset I) (m : ℕ) : ∀ᵐa ∂(allocationPMF E m).toMeasure,a∈(allocationPMF E m).support := by
  have h := ae_restrict_mem (μ:=(allocationPMF E m).toMeasure) ((allocationPMF E m).support_countable.measurableSet)
  rw [PMF.restrict_toMeasure_support] at h
  exact h

lemma gridAllocation_support_ae {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ)
    (p : BridgeEndpoints N L×(Fin N→Bool)) :
    ∀ᵐa ∂gridAllocationKernel hL q p,∀v,a v∈(allocationPMF (recordedList hL v p) q).support := by
  rw [gridAllocationKernel_apply]
  apply ae_all_iff.mpr
  intro v
  exact (MeasureTheory.measurePreserving_eval (fun w ↦ (allocationPMF (recordedList hL w p) q).toMeasure) v).quasiMeasurePreserving.tendsto_ae
    (allocation_support_ae _ _)

lemma groups_disjoint_ae {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) :
    ∀ᵐa ∂gridAllocationKernel hL (G*M) p,∀g h : Fin G,g≠h→Disjoint (groupUnion g a) (groupUnion h a) := by
  filter_upwards [gridAllocation_support_ae hL (G*M) p] with a ha
  exact fun g h hgh ↦ groups_disjoint hL p a ha g h hgh

lemma pi_failure_sets {V A : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace A]
    (μ : V→Measure A) [∀v,IsProbabilityMeasure (μ v)] (E : V→Set A) (S : Finset V) :
    (Measure.pi μ) {a | ∀v∈S,a v∈E v}=∏v∈S,μ v (E v) := by
  classical
  have he : {a : V→A | ∀v∈S,a v∈E v}=Set.pi Set.univ (fun v ↦ if v∈S then E v else Set.univ) := by
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,true_implies]
    constructor
    · intro h v; by_cases hv : v∈S <;> simp [hv,h v]
    · intro h v hv; simpa [hv] using h v
  rw [he,Measure.pi_pi]
  simp only [apply_ite,measure_univ]
  exact Fintype.prod_ite_mem S (fun v ↦ μ v (E v))

lemma grid_group_law {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) (v : Fin 3→Fin K) (g : Fin G)
    (hsize : G*M≤(recordedList hL v p).card) :
    (gridAllocationKernel hL (G*M) p).map
      (fun a ↦ Option.map (fun f ↦ (groupPosition M G g).trans f) (a v))=
      (allocationPMF (recordedList hL v p) M).toMeasure := by
  rw [gridAllocationKernel_apply]
  have he := (measurePreserving_eval (fun w ↦ (allocationPMF (recordedList hL w p) (G*M)).toMeasure) v).map_eq
  change (Measure.pi (fun w ↦ (allocationPMF (recordedList hL w p) (G*M)).toMeasure)).map (fun a ↦ a v) =
    (allocationPMF (recordedList hL v p) (G*M)).toMeasure at he
  have hf : Measurable (fun a : GridAllocation N K (G*M) ↦ a v) := measurable_pi_apply v
  have hg : Measurable (Option.map (fun f : Fin (G*M)↪Fin N ↦ (groupPosition M G g).trans f)) :=
    measurable_of_countable _
  calc
    _ = ((Measure.pi (fun w ↦ (allocationPMF (recordedList hL w p) (G*M)).toMeasure)).map
        (fun a : GridAllocation N K (G*M) ↦ a v)).map
        (Option.map (fun f : Fin (G*M)↪Fin N ↦ (groupPosition M G g).trans f)) :=
      (Measure.map_map hg hf).symm
    _ = _ := by
      rw [he,PMF.toMeasure_map _ _ hg,allocated_group_uniform _ _ _ hsize]

end HardSphere.Groups

end
end

end

end OAI
