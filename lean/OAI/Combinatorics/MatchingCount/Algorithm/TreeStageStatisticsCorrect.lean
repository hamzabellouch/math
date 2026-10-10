import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStageStatistics
import OAI.Combinatorics.MatchingCount.Algorithm.TreeObservablesCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableEstimator
open TreeFraction

lemma mean_ofFn {S : ℕ} (f : Fin S→ℚ) (hf : ∀ i,0≤f i) :
    mean (List.ofFn (fun i=>TreeFraction.repr (f i)))=TreeFraction.repr ((∑ i,f i)/(S:ℚ)) := by
  have he : List.ofFn (fun i=>TreeFraction.repr (f i))=(List.ofFn f).map TreeFraction.repr :=
    by rw [List.map_ofFn]; rfl
  rw [he,mean_rep _ (by intro a ha; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha; exact hf i)]
  simp only [List.sum_ofFn,List.length_ofFn]
end MatchingFPRAS.ExecutableEstimator

namespace MatchingFPRAS.ExecutableStatistics
open TreeTyped TreeFraction ExecutableMarking ExecutableEstimator

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]
variable {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
def sampleRep : List (Marks E) := List.ofFn (fun i=>marksRep (s i) (m i))
def scalarA (i : Fin S) : ℚ := if ∀ e∈s i,m i e=0 then 1 else 0
def scalarD (r : E→ℚ) (i : Fin S) : ℚ := if ∀ e∈s i,m i e=0 then ∏ e∈s i,r e else 0
def scalarProbe (r : E→ℚ) (e : E) (i : Fin S) : ℚ :=
  if e∈s i ∧ ∀ a∈s i,m i a=if a=e then 2 else 0 then ∏ a∈s i\{e},r a else 0
omit [Codec C] [Codec E] [Inhabited E] [LinearOrder E] in
lemma scalarA_nonneg [LinearOrder E] (i : Fin S) : 0 ≤ scalarA s m i := by unfold scalarA; split_ifs <;> norm_num
omit [Codec C] [Codec E] [Inhabited E] [LinearOrder E] in
lemma scalarD_nonneg [LinearOrder E] (r : E→ℚ) (hr : ∀ e,0≤r e) (i : Fin S) : 0 ≤ scalarD s m r i := by
  unfold scalarD; split_ifs; exact Finset.prod_nonneg (fun e _=>hr e); exact le_rfl
omit [Codec C] [Codec E] [Inhabited E] in
lemma scalarProbe_nonneg (r : E→ℚ) (hr : ∀ e,0≤r e) (e : E) (i : Fin S) :
    0 ≤ scalarProbe s m r e i := by
  unfold scalarProbe; split_ifs; exact Finset.prod_nonneg (fun a _=>hr a); exact le_rfl

omit [Codec E] [Inhabited E] in
lemma averageA_rep [Codec E] [Inhabited E] :
    averageA (sampleRep s m)=TreeFraction.repr ((∑ i,scalarA s m i)/(S:ℚ)) := by
  unfold averageA sampleRep
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableA_rep]
  exact mean_ofFn (scalarA s m) (scalarA_nonneg s m)
omit [Codec C] [Codec E] [Inhabited E] in
lemma averageD_rep [Codec C] [Codec E] [Inhabited E] (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e)) :
    averageD q (c,sampleRep s m)=TreeFraction.repr ((∑ i,scalarD s m r i)/(S:ℚ)) := by
  unfold averageD sampleRep
  dsimp only
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableD_rep q c r hr hq]
  exact mean_ofFn (scalarD s m r) (scalarD_nonneg s m r hr)
omit [Codec C] [Codec E] [Inhabited E] in
lemma averageProbe_rep [Codec C] [Codec E] [Inhabited E] (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e)) (e : E) :
    averageProbe q ((c,e),sampleRep s m)=TreeFraction.repr ((∑ i,scalarProbe s m r e i)/(S:ℚ)) := by
  unfold averageProbe sampleRep
  dsimp only
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableProbe_rep q c r hr hq]
  exact mean_ofFn (scalarProbe s m r e) (scalarProbe_nonneg s m r hr e)

lemma estimates_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e)) (D : ℕ) (keys : List E) :
    estimates q ((c,(D,keys)),sampleRep s m)=
      (TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m r i)/(S:ℚ))),
       keys.map (fun e=>(e,TreeFraction.repr (Counting.upperEstimate D
         ((∑ i,scalarD s m r i)/(S:ℚ)) ((∑ i,scalarProbe s m r e i)/(S:ℚ)))))) := by
  have ha : 0≤(∑ i,scalarA s m i)/(S:ℚ):=div_nonneg (Finset.sum_nonneg (fun i _=>scalarA_nonneg s m i)) (Nat.cast_nonneg _)
  have hd : 0≤(∑ i,scalarD s m r i)/(S:ℚ):=div_nonneg (Finset.sum_nonneg (fun i _=>scalarD_nonneg s m r hr i)) (Nat.cast_nonneg _)
  have hz (e : E) : 0≤(∑ i,scalarProbe s m r e i)/(S:ℚ):=div_nonneg
    (Finset.sum_nonneg (fun i _=>scalarProbe_nonneg s m r hr e i)) (Nat.cast_nonneg _)
  unfold estimates
  dsimp only
  rw [averageD_rep s m q c r hr hq,averageA_rep s m,ratio_rep _ _ ha hd]
  congr 1
  apply List.map_congr_left
  intro e _he
  unfold estimateProbe
  dsimp only
  rw [averageProbe_rep s m q c r hr hq e,upper_rep D _ _ hd (hz e)]
end MatchingFPRAS.ExecutableStatistics

end OAI
