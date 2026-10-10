import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.VirtualCast
import OAI.Combinatorics.KMedianRecovery.Algorithms.CompletionResultGuarantee

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
noncomputable def result (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (bits : BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Explicit.exponent s.leaves.length)
      (Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) :=
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  BinaryCompletionFair.result F S s.deleted CopyGround.part (CopyGround.part_surjective (balls δ F s) hH)
    (CopyGround.origin (balls δ F s) hH) loc (SortedIndex.enum red) sel dest k
    (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
    (fun i e=>δ (SortedIndex.enum D i) (loc e))
    (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
    (fun i=>RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i))
    (fun i e=>δ (SortedIndex.enum red i) (loc e)) bits
noncomputable def objective (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (X : Finset (Fin (s.leaves.length*n))) : ℝ :=
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  surrogate (∑ j,(RationalSampling.assignmentWeight δ D S Δ s (sel j)*δ (sel j) (dest j):ℚ)) k
    (fun i=>(RationalSampling.reference δ S Δ s (SortedIndex.enum D i):ℝ))
    (fun i e=>(δ (SortedIndex.enum D i) (loc e):ℝ))
    (fun i=>(RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i):ℝ))
    (fun i=>(RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i):ℝ))
    (fun i e=>(δ (SortedIndex.enum red i) (loc e):ℝ)) X
variable [PseudoMetricSpace (Fin n)]
lemma result_guarantee (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (hdel : s.deleted⊆S)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (hr : ∀ i,0≤ s.radius i)
    (sel dest : Fin m→Fin n) (c k : ℕ)
    (hinj : Function.Injective sel) (hsel : ∀ j,sel j∈(S\s.deleted).filter (fun i=>colors i=2))
    (hdest : ∀ j,dest j∈F) (hcountDest : (Finset.univ.image dest).card≤c)
    (hcount : s.leaves.length+c≤ s.deleted.card+k+m)
    (hk : k≤((S\s.deleted).filter (fun i=>colors i=1)).card) :
    (∀ bits,result δ D F S Δ s colors hH sel dest k bits⊆F ∧
      (result δ D F S Δ s colors hH sel dest k bits).card=S.card ∧
      (result δ D F S Δ s colors hH sel dest k bits).Nonempty) ∧
    ∀ X,PartitionFeasible CopyGround.part X →
      average (fun bits=>realCost D (result δ D F S Δ s colors hH sel dest k bits))≤
        (38/100:ℝ)*objective δ D F S Δ s colors hH sel dest k ∅+
        (62/100:ℝ)*objective δ D F S Δ s colors hH sel dest k X := by
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  have hloc (e : Fin (s.leaves.length*n)) : loc e∈F :=
    (Finset.mem_filter.mp (CopyGround.location_mem (balls δ F s) hH e)).1
  have hball (e : Fin (s.leaves.length*n)) : dist (s.center (CopyGround.part e)) (loc e)≤ s.radius (CopyGround.part e) := by
    have hh:=(Finset.mem_filter.mp (CopyGround.location_mem (balls δ F s) hH e)).2
    change δ (s.center (CopyGround.part e)) (loc e)≤ s.leaves[(CopyGround.part e).val].2 at hh
    exact (hδ _ _ ▸ Rat.cast_le.mpr hh)
  have hredMem (i : Fin red.card) : SortedIndex.enum red i∈S\s.deleted :=
    (Finset.mem_filter.mp (SortedIndex.enum_mem red i)).1
  have hredColor (i : Fin red.card) : colors (SortedIndex.enum red i)=1 :=
    (Finset.mem_filter.mp (SortedIndex.enum_mem red i)).2
  have hblueColor (j : Fin m) : colors (sel j)=2 := (Finset.mem_filter.mp (hsel j)).2
  have hRB (i : Fin red.card) (j : Fin m) : SortedIndex.enum red i≠sel j := by
    intro he
    have hh:=hredColor i
    rw [he,hblueColor] at hh
    exact (by decide : (2:Fin 3)≠1) hh
  have hGR (i : Fin red.card) : SortedIndex.enum red i∉green := by
    intro hh
    have hz:=(Finset.mem_filter.mp hh).2
    rw [hredColor] at hz
    exact (by decide : (1:Fin 3)≠0) hz
  have hGB (j : Fin m) : sel j∉green := by
    intro hh
    have hz:=(Finset.mem_filter.mp hh).2
    rw [hblueColor] at hz
    exact (by decide : (2:Fin 3)≠0) hz
  have hK : (∑ j,assignmentWeight D (s.assignment S Δ) (sel j)*dist (sel j) (dest j))≤
      (∑ j,(RationalSampling.assignmentWeight δ D S Δ s (sel j)*δ (sel j) (dest j):ℚ):ℚ) := by
    simp only [Rat.cast_sum,Rat.cast_mul,hδ,RationalSampling.assignment_array_cast δ hδ]
    exact le_rfl
  have hbase (i : Fin D.card) := RationalSampling.reference_array_cast δ hδ S Δ s (SortedIndex.enum D i)
  have hweight (i : Fin red.card) := RationalSampling.assignment_array_cast δ hδ D S Δ s (SortedIndex.enum red i)
  have hredBase (i : Fin red.card) :
      (RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i):ℝ)=
      virtualNearest green s.center s.radius (Δ:ℝ) (SortedIndex.enum red i) := by
    have hew : (⟨∅,s.leaves⟩ : RationalSampling.State n).center=s.center := rfl
    have her : (⟨∅,s.leaves⟩ : RationalSampling.State n).radius=s.radius := rfl
    simpa only [Finset.sdiff_empty,hew,her] using RationalSampling.reference_array_cast δ hδ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i)
  have hw (i : Fin red.card) : 0≤RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i) := by
    unfold RationalSampling.assignmentWeight
    positivity
  simpa only [result,objective,Rat.cast_sum] using BinaryCompletionFair.result_guarantee D F S s.deleted green hSF hS hdel CopyGround.part
    (CopyGround.origin (balls δ F s) hH) (CopyGround.part_origin (balls δ F s) hH) loc s.center s.radius (Δ:ℝ)
    (s.assignment S Δ) (s.assignment_mem S Δ) (s.assignment_distance S Δ) hr (Rat.cast_nonneg.mpr hΔ)
    hloc hball (fun x f hf=>hδ x f ▸ Rat.cast_le.mpr (hbound x f hf))
    (SortedIndex.enum red) sel dest (SortedIndex.enum_injective red) hinj hredMem
    (fun j=>(Finset.mem_filter.mp (hsel j)).1) hRB (Finset.filter_subset _ _) hGR hGB hdest c k hcountDest hcount hk
    _ hK _ _ _ _ _ hbase (fun i e=>hδ _ _) hweight hredBase (fun i e=>hδ _ _)
    (CopyGround.part_surjective (balls δ F s) hH) hw
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

namespace MetricKMedianRecovery.Completion
variable {P P' R R' E : Type*} [Fintype P] [Fintype P'] [Fintype R] [Fintype R']

lemma bottomSum_equiv (e : R≃R') (k : ℕ) (v : R'→ℝ) : bottomSum k (v ∘ e)=bottomSum k v := by
  classical
  apply le_antisymm
  · obtain ⟨S,hS,hv⟩:=bottomSum_attained k v
    have hc : (S.map e.symm.toEmbedding).card=min k (Fintype.card R) := by
      simpa only [Finset.card_map,Fintype.card_congr e] using hS
    have hh:=bottomSum_le (v ∘ e) hc
    simpa only [Finset.sum_map,Equiv.toEmbedding_apply,Function.comp_apply,Equiv.apply_symm_apply,hv] using hh
  · obtain ⟨S,hS,hv⟩:=bottomSum_attained k (v ∘ e)
    have hc : (S.map e.toEmbedding).card=min k (Fintype.card R') := by
      simpa only [Finset.card_map,←Fintype.card_congr e] using hS
    have hh:=bottomSum_le v hc
    simp only [Finset.sum_map,Equiv.toEmbedding_apply] at hh
    simpa only [Function.comp_def] using hh.trans_eq hv
lemma surrogate_reindex (ep : P≃P') (er : R≃R') (K : ℝ) (k : ℕ) (base : P'→ℝ)
    (distance : P'→E→ℝ) (weight redBase : R'→ℝ) (redDistance : R'→E→ℝ) (X : Finset E) :
    surrogate K k (base ∘ ep) (distance ∘ ep) (weight ∘ er) (redBase ∘ er) (redDistance ∘ er) X=
      surrogate K k base distance weight redBase redDistance X := by
  unfold surrogate
  have hp:=Equiv.sum_comp ep (fun p=>cappedCost (base p) (distance p) X)
  have hr:=bottomSum_equiv er k (fun r=>weight r*cappedCost (redBase r) (redDistance r) X)
  simp only [Function.comp_def] at hp hr ⊢
  rw [hp,hr]
end MetricKMedianRecovery.Completion
namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
noncomputable def equiv (S : Finset α) : Fin S.card≃S :=
  Equiv.ofBijective (fun i=>⟨enum S i,enum_mem S i⟩) (by
    constructor
    · intro i j h
      exact enum_injective S (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      have hh : x∈List.ofFn (enum S) := by rw [enum_list];simpa only [Finset.mem_sort] using hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hh
      exact ⟨i,Subtype.ext hi⟩)
lemma equiv_val (S : Finset α) (i : Fin S.card) : (equiv S i).val=enum S i := rfl
end MetricKMedianRecovery.SortedIndex

end OAI
