import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStatistics

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics ExecutableLadder UnitRefresh

variable {E : Type} [Fintype E] [LinearOrder E]
lemma probe_numbered (s : Finset E) (m : E→Fin 3) (e : E) :
    (index e∈Numbered.set s ∧ ∀ a∈Numbered.set s,extend 0 m a=if a=index e then 2 else 0) ↔
    (e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0) := by
  have hm : index e∈Numbered.set s ↔ e∈s := by
    simp only [Numbered.set,Finset.mem_map,Numbered.embedding,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,he⟩
      exact index_injective he ▸ ha
    · intro h; exact ⟨e,h,rfl⟩
  rw [hm]
  apply and_congr_right
  intro _he
  constructor
  · intro h a ha
    have hh:=h (index a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
    simpa only [extend_index,index_injective.eq_iff] using hh
  · intro h a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    simpa only [Numbered.embedding,Function.Embedding.coeFn_mk,extend_index,index_injective.eq_iff] using h b hb

lemma scalarProbe_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
    (r : E→ℚ) (e : E) (i : Fin S) :
    scalarProbe (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) (extend 1 r) (index e) i=
      scalarProbe s m r e i := by
  by_cases h : e∈s i ∧ ∀ a∈s i,m i a=if a=e then 2 else 0
  · have hh:=(probe_numbered (s i) (m i) e).mpr h
    simp only [scalarProbe,ite_eq_left h,ite_eq_left hh]
    have hs : Numbered.set (s i)\{index e}=Numbered.set (s i\{e}) := by
      simp only [Numbered.set,Finset.map_sdiff,Finset.map_singleton,Numbered.embedding,
        Function.Embedding.coeFn_mk]
    rw [hs]
    simp only [Numbered.set,Finset.prod_map,Numbered.embedding,Function.Embedding.coeFn_mk,extend_index]
  · have hh : ¬(index e∈Numbered.set (s i) ∧ ∀ a∈Numbered.set (s i),
      extend 0 (m i) a=if a=index e then 2 else 0) := fun hh=>h ((probe_numbered _ _ _).mp hh)
    simp only [scalarProbe,ite_eq_right h,ite_eq_right hh]

noncomputable def reweightsRep (r : E→ℚ) : Reweights :=
  (List.ofFn (orderedEnum E)).map (fun e=>(index e,TreeFraction.repr (r e)))
lemma reweight_rep (r : E→ℚ) (i : ℕ) :
    reweight (reweightsRep r,i)=TreeFraction.repr (extend 1 r i) := by
  by_cases h : i<Fintype.card E
  · let e := orderedEnum E ⟨i,h⟩
    have he : index e=i := by simp [e,index]
    change ExecutableLadder.lookup (1,1) (reweightsRep r,i)=_
    rw [←he]
    unfold reweightsRep
    rw [lookup_image (1,1) (List.ofFn (orderedEnum E)) index (fun e=>TreeFraction.repr (r e))
      index_injective e (List.mem_ofFn.mpr ⟨⟨i,h⟩,rfl⟩),extend_index]
  · have hoff : ∀ p∈reweightsRep r,p.1≠i := by
      intro p hp
      obtain ⟨e,_he,rfl⟩:=List.mem_map.mp hp
      intro heq
      have hi : index e<Fintype.card E := ((orderedEnum E).symm e).isLt
      exact h (heq ▸ hi)
    change lookup (1,1) (reweightsRep r,i)=_
    have hout : lookup (1,1) (reweightsRep r,i)=(1,1) := by
      unfold reweightsRep
      apply lookup_off
      intro e _he hi
      exact h (hi ▸ ((orderedEnum E).symm e).isLt)
    rw [hout]
    simp only [extend,dite_eq_right h]
    rfl

lemma extend_nonneg (r : E→ℚ) (hr : ∀ e,0≤r e) : ∀ i,0≤extend 1 r i := by
  intro i
  unfold extend
  split_ifs
  · exact hr _
  · norm_num

lemma statistics_rep {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
    (r : E→ℚ) (hr : ∀ e,0≤r e) (D : ℕ) (keys : List E) :
    statistics ((reweightsRep r,(D,keys.map index)),List.ofFn (fun i=>numericMarks (s i) (m i)))=
      (TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m r i)/(S:ℚ))),
       keys.map (fun e=>(index e,TreeFraction.repr (Counting.upperEstimate D
         ((∑ i,scalarD s m r i)/(S:ℚ)) ((∑ i,scalarProbe s m r e i)/(S:ℚ)))))) := by
  have hs : List.ofFn (fun i=>numericMarks (s i) (m i))=
      sampleRep (fun i=>Numbered.set (s i)) (fun i=>extend 0 (m i)) := by
    simp only [sampleRep,numericMarks_eq]
  rw [statistics,hs,estimates_rep (fun i=>Numbered.set (s i)) (fun i=>extend 0 (m i))
    reweight (reweightsRep r) (extend 1 r) (extend_nonneg r hr) (reweight_rep r) D (keys.map index)]
  simp only [scalarA_numbered,scalarD_numbered,List.map_map,Function.comp_def,scalarProbe_numbered]

end MatchingFPRAS.NumericMarking

end OAI
