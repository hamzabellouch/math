import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingReference
import OAI.Combinatorics.KMedianRecovery.Sampling.RationalSampling

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
open BitMachine BinarySamplingReference
variable {n l : ℕ}
def fromArrays (T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) : State n :=
  ⟨T,List.ofFn (fun j=>(v j,r j))⟩
lemma key_real (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (s : State n) (w i : Fin n) :
    key δ Δ s w (realTag i)=toLex (δ w i,i.val) := rfl
lemma key_dummy (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (s : State n) (w : Fin n) :
    key δ Δ s w (leafTag 0)=toLex (Δ,n) := rfl
lemma key_leaf (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (T : Finset (Fin n))
    (v : Fin l→Fin n) (r : Fin l→ℚ) (w : Fin n) (j : Fin l) :
    key δ Δ (fromArrays T v r) w (leafTag (j.val+1))=toLex (δ w (v j)+r j,n+j.val+1) := by
  simp only [key,tagDistance,fromArrays,leafTag,ofLex_toLex,List.getElem?_ofFn,dite_eq_left j.isLt,tagId,Nat.add_assoc]
lemma tags_fromArrays (S T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) :
    Sampling.tags S (fromArrays T v r).real=
      (S\T).image realTag ∪ (Finset.range (l+1)).image leafTag := by
  simp only [Sampling.tags,fromArrays,State.real,List.length_map,List.length_ofFn]
lemma values_finset (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (S T : Finset (Fin n))
    (v : Fin l→Fin n) (r : Fin l→ℚ) (w : Fin n) :
    (values Δ (S\T) v r (δ w)).toFinset=keys δ S Δ (fromArrays T v r) w := by
  ext x
  simp only [List.mem_toFinset,values,List.mem_append,List.mem_map,Finset.mem_sort,List.mem_cons,List.mem_ofFn,
    keys,Finset.mem_image,tags_fromArrays,Finset.mem_union]
  constructor
  · rintro (⟨i,hi,hx⟩ | hx | ⟨j,hx⟩)
    · exact ⟨realTag i,Or.inl ⟨i,hi,rfl⟩,by simpa only [key_real] using hx⟩
    · exact ⟨leafTag 0,Or.inr ⟨0,Finset.mem_range.mpr (by omega),rfl⟩,by rw [key_dummy];exact hx.symm⟩
    · exact ⟨leafTag (j.val+1),Or.inr ⟨j.val+1,Finset.mem_range.mpr (by omega),rfl⟩,by rw [key_leaf];exact hx⟩
  · rintro ⟨t,(⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩),hx⟩
    · exact Or.inl ⟨i,hi,by simpa only [key_real] using hx⟩
    · have hj' : j<l+1 := Finset.mem_range.mp hj
      cases j with
      | zero=>exact Or.inr (Or.inl (by simpa only [key_dummy] using hx.symm))
      | succ j=>
        let j' : Fin l:=⟨j,by omega⟩
        change key δ Δ (fromArrays T v r) w (leafTag (j'.val+1))=x at hx
        rw [key_leaf] at hx
        exact Or.inr (Or.inr ⟨j',hx⟩)
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma run_chosen (Δ : ℚ) (S T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (w : Fin n) :
    BinarySamplingReference.run (pack Δ (S\T) v r (δ w))=
      BinaryRationalSort.entryBits (key δ Δ (fromArrays T v r) w
        (Sampling.chosen S (Δ:ℝ) (fromArrays T v r).real w)) := by
  rw [BinarySamplingReference.run_pack]
  simp only [values_finset]
  rw [minimum_key δ hδ]
lemma run_reference (Δ : ℚ) (S T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (w : Fin n) :
    (BinaryRational.decode (extractPrefix
      (BinarySamplingReference.run (pack Δ (S\T) v r (δ w)))):ℝ)=
        Sampling.reference S (Δ:ℝ) (fromArrays T v r).real w := by
  rw [run_chosen δ hδ]
  simp only [BinaryRationalSort.entryBits,extractPrefix_pairBits,BinaryRational.decode_encode,key,ofLex_toLex]
  exact tagDistance_cast δ hδ Δ _ w _
lemma run_tagId (Δ : ℚ) (S T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (w : Fin n) :
    BinaryArithmetic.value (discardPrefix
      (BinarySamplingReference.run (pack Δ (S\T) v r (δ w))))=
      tagId (Sampling.chosen S (Δ:ℝ) (fromArrays T v r).real w) := by
  rw [run_chosen δ hδ]
  simp only [BinaryRationalSort.entryBits,discardPrefix_pairBits,BinaryArithmetic.value_bits,key,ofLex_toLex]
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
