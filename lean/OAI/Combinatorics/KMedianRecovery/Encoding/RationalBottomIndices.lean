import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
noncomputable def indexSet {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i=>ranking v i∈Completion.bottomSet (Finset.univ.image (ranking v)) k)
lemma indexSet_image {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (indexSet v k).image (ranking v)=Completion.bottomSet (Finset.univ.image (ranking v)) k := by
  classical
  ext p
  simp only [Finset.mem_image,indexSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hp
    obtain ⟨i,_,he⟩:=Finset.mem_image.mp (Completion.bottomSet_subset _ _ hp)
    exact ⟨i,he ▸ hp,he⟩
lemma indexSet_card {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : (indexSet v k).card=min k r := by
  rw [←Finset.card_image_of_injective _ (ranking_injective v),indexSet_image,Completion.bottomSet_card,
    Finset.card_image_of_injective _ (ranking_injective v),Finset.card_univ,Fintype.card_fin]
lemma indexSet_sum {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    ∑ i∈indexSet v k,(v i:ℝ)=Completion.bottomSum k (fun i=>(v i:ℝ)) := by
  classical
  rw [←bottom_sum_cast]
  have hn:=((Finset.univ.image (ranking v)).sort_nodup (·≤·)).sublist (List.take_sublist k _)
  have h:=List.sum_toFinset (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) hn
  rw [show (((Finset.univ.image (ranking v)).sort (·≤·)).take k).toFinset=
    (indexSet v k).image (ranking v) from (indexSet_image v k).symm,
    Finset.sum_image (ranking_injective v).injOn] at h
  rw [Rat.cast_list_sum]
  simpa only [bottomValues,List.map_map,Function.comp_def,ranking,ofLex_toLex] using h
noncomputable def rawIndices (x : List Bool) : List Bool :=
  mapWith (fun y=>discardPrefix (discardPrefix y)) (pairBits ([],bottom x))
noncomputable def rawIndices_computes : PolyComputes rawIndices := by
  have rawIndicesComputes :=
    ((const_computes []).pair bottom_computes).comp
      (mapWith_computes (discardPrefix_computes.comp discardPrefix_computes))
  unfold rawIndices
  simpa only [Function.comp_def] using rawIndicesComputes
def bottomIndices {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : List ℕ :=
  (((Finset.univ.image (ranking v)).sort (·≤·)).take k).map (fun p=>(ofLex p).2)
lemma bottomIndices_finset {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (bottomIndices v k).toFinset=(indexSet v k).image Fin.val := by
  classical
  have hm (xs : List (ℚ ×ₗ ℕ)) : (xs.map (fun p=>(ofLex p).2)).toFinset=xs.toFinset.image (fun p=>(ofLex p).2) := by
    ext i; simp
  rw [bottomIndices,hm,show (((Finset.univ.image (ranking v)).sort (·≤·)).take k).toFinset=
    (indexSet v k).image (ranking v) from (indexSet_image v k).symm,Finset.image_image]
  rfl
lemma rawIndices_pack {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    rawIndices (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
      encode ((bottomIndices v k).map Nat.bits) := by
  simp only [rawIndices,bottom_pack,mapWith_encode,List.map_map,Function.comp_def,
    discardPrefix_pairBits,entryBits,bottomIndices]
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
