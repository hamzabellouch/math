import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedBind
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedDraws
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPermutationExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FixedSizeSampleCells

namespace OAI

/-! # Building sampled subsets from stored permutation entries

The sampled permutation is materialized and its first selected entries are
scanned into a duplicate-free list. The Finset constructor uses that list
without a further deduplication pass.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

abbrev PermutationAccepted (n g : ℕ) := Accepted (permutationCoupling n g)

theorem permutation_materializes (n g : ℕ) (a : PermutationAccepted n g) :
    ∃ v, (PermutationSamplerCells.materialize n g a.seed.val).1.1 = some v := by
  have hv := PermutationDigitsExecution.value n g a.seed.val
  rw [(SamplerExecution.permutation n g).value_eq,accepted_source a] at hv
  cases hd : (PermutationDigitsExecution.run n g a.seed.val).value with
  | none => simp only [hd,Option.map_none,reduceCtorEq] at hv
  | some d =>
    refine ⟨(PermutationArray.build g d).1,?_⟩
    rw [PermutationSamplerCells.materialize_value]
    simp only [PermutationDigitsExecution.materialize,hd]

theorem permutation_materialized_value (n g : ℕ) (a : PermutationAccepted n g)
    (v : Vector (Fin g) g)
    (hv : (PermutationSamplerCells.materialize n g a.seed.val).1.1 = some v) :
    ∀ i : Fin g, v[i.val] = a.value i := by
  rw [PermutationSamplerCells.materialize_value] at hv
  obtain ⟨e,he,hv⟩ := PermutationDigitsExecution.materialize_value n g a.seed.val v hv
  rw [(SamplerExecution.permutation n g).value_eq,accepted_source a] at he
  cases Option.some.inj he
  exact hv

abbrev Materialized (n g : ℕ) (a : PermutationAccepted n g) :=
  {v : Vector (Fin g) g //
    (PermutationSamplerCells.materialize n g a.seed.val).1.1 = some v}

def materializeAccepted (n g : ℕ) (a : PermutationAccepted n g) :
    (Materialized n g a × ℕ) × ℕ :=
  let r := PermutationSamplerCells.materialize n g a.seed.val
  match h : r.1.1 with
  | none => False.elim (by
      obtain ⟨v,hv⟩ := permutation_materializes n g a
      cases h.symm.trans hv)
  | some v => ((⟨v,h⟩,g*n^3+r.1.2+1),r.2+8)

def selectedCompute (n g k : ℕ) (_hk : k ≤ g) (a : PermutationAccepted n g) :
    (Finset (Fin g) × ℕ) × ℕ :=
  let material := materializeAccepted n g a
  let v := material.1.1
  let xs := FixedSizeSampleCells.selected v.val k
  let set : Finset (Fin g) := ⟨(xs.1 : Multiset (Fin g)),by
    rw [FixedSizeSampleCells.prefix_value]
    change (((List.finRange g).filter (fun i => decide (i.val < k))).map
      (fun i => v.val[i.val])).Nodup
    apply List.Nodup.map
    · intro i j h
      have hv := permutation_materialized_value n g a v.val v.property
      exact a.value.injective ((hv i).symm.trans (h.trans (hv j)))
    · exact (List.nodup_finRange g).filter _⟩
  ((set,material.1.2+4*g+3),material.2+xs.2+g+8)

theorem selectedCompute_value (n g k : ℕ) (hk : k ≤ g) (a : PermutationAccepted n g) :
    (selectedCompute n g k hk a).1.1 = (permutationBlock (initialSubset g k hk) a.value).val := by
  let v := (materializeAccepted n g a).1.1
  have hv := permutation_materialized_value n g a v.val v.property
  have h := PermutationSubsetCode.prefix_value v.val a.value hv k hk
  apply Finset.ext
  intro i
  change i ∈ (FixedSizeSampleCells.selected v.val k).1 ↔ _
  rw [FixedSizeSampleCells.prefix_value]
  have hm := Finset.ext_iff.mp h i
  simpa only [List.mem_toFinset,permutationBlock] using hm

theorem selectedCompute_work (n g k : ℕ) (hk : k ≤ g) (a : PermutationAccepted n g) :
    (selectedCompute n g k hk a).1.2 ≤ g*n^3+10*(g+1)^2+4*g+5 := by
  have hm := PermutationDigitsExecution.materialize_work n g a.seed.val
  rw [←PermutationSamplerCells.materialize_value] at hm
  obtain ⟨v,hv⟩ := permutation_materializes n g a
  unfold selectedCompute materializeAccepted
  dsimp only
  split
  next h => cases h.symm.trans hv
  · dsimp only
    omega

theorem selectedCompute_cells (n g k : ℕ) (hk : k ≤ g) (a : PermutationAccepted n g) :
    (selectedCompute n g k hk a).2 ≤ (g+1)*(3*n^3+128)+6*g+32 := by
  have hm := PermutationSamplerCells.materialize_cells n g a.seed.val
  obtain ⟨v,hv⟩ := permutation_materializes n g a
  unfold selectedCompute materializeAccepted
  dsimp only
  split
  next h => cases h.symm.trans hv
  next v' h =>
    have hx := FixedSizeSampleCells.prefix_cells v' k
    dsimp only
    omega

def selectedTyped (n g k : ℕ) (hk : k ≤ g) (a : PermutationAccepted n g) :
    (↥((Finset.univ : Finset (Fin g)).powersetCard (initialSubset g k hk).card) × ℕ) × ℕ :=
  let r := selectedCompute n g k hk a
  ((⟨r.1.1,by
    rw [selectedCompute_value]
    exact (permutationBlock (initialSubset g k hk) a.value).property⟩,r.1.2),r.2)

theorem selectedTyped_value (n g k : ℕ) (hk : k ≤ g) (a : PermutationAccepted n g) :
    (selectedTyped n g k hk a).1.1 = permutationBlock (initialSubset g k hk) a.value := by
  apply Subtype.ext
  exact selectedCompute_value n g k hk a

def subsetInitial (w n g k : ℕ) (hk : k ≤ g) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.subset w n g (initialSubset g k hk) hw) :=
  mapStored (permutation w n g hw) (permutationBlock (initialSubset g k hk))
    (selectedTyped n g k hk) (selectedTyped_value n g k hk)

def fixedSize (w n g k : ℕ) (hk : k ≤ g) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.fixedSize w n g k hk hw) :=
  map (subsetInitial w n g k hk hw) (initialSubsetEquiv g k hk)
    (fun a => (((initialSubsetEquiv g k hk) a,1),2)) (fun _ => rfl)

theorem fixedSize_bounded (w n g k : ℕ) (hk : k ≤ g) (hw : Nat.clog 2 g ≤ w) :
    (fixedSize w n g k hk hw).Bounded
      (g*(14*n^3+5*g+68)+10*(g+1)^2+11)
      (10*(g+1)*(n^3+256)) (10*(g+1)*(n^3+256)) := by
  have hs := mapStored_bounded (permutation w n g hw)
    (permutationBlock (initialSubset g k hk)) (selectedTyped n g k hk)
    (selectedTyped_value n g k hk) _ _ _ _ _ (permutation_bounded w n g hw)
    (selectedCompute_work n g k hk) (selectedCompute_cells n g k hk)
  have ht := map_bounded (subsetInitial w n g k hk hw) (initialSubsetEquiv g k hk)
    (fun a => (((initialSubsetEquiv g k hk) a,1),2)) (fun _ => rfl)
    _ _ _ 1 2 hs (fun _ => le_rfl) (fun _ => le_rfl)
  intro stream cursor
  have h := ht stream cursor
  change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
  refine ⟨h.1.trans (by nlinarith),h.2.1.trans ?_,h.2.2.trans ?_⟩
  · apply max_le
    · apply max_le <;> nlinarith
    · nlinarith
  · nlinarith

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
