import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBackgroundPreparation

namespace OAI

/-! # Exact blocks produced by the background preparation -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationBackgroundPreparation

open scoped BigOperators
variable {n : ℕ}

theorem size_check (I : Instance n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (guesses : Vector ℕ 3)
    (g : RepresentationSetup.Guesses n) (hg : ∀ j : Fin 3, guesses[j.val] = (g j).val)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    (∑ i : Fin 8, (RepresentationAllocationExecution.run n guesses).1[i.val]) =
      (CanonicalBackground.run v).1.length := by
  have hs := representationLeafCounts_sum g hn hlog
  have hv' := CanonicalBackground.value I v e hv ∅
  calc
    _ = ∑ i : Fin 8, representationLeafCounts n g i :=
      Finset.sum_congr rfl (fun i _ => RepresentationAllocationExecution.value n guesses g hg i)
    _ = representationBackgroundSize n := hs
    _ = _ := by
      rw [hv', Finset.length_sort, RepresentationSetup.backgroundDomain_card]

theorem complete (I : Instance n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (signs : Finset (Fin n)) (guesses : Vector ℕ 3)
    (g : RepresentationSetup.Guesses n) (hg : ∀ j : Fin 3, guesses[j.val] = (g j).val)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ∃ rows, (run I v guesses).1 = some rows ∧
      ∀ (side : Fin 2) (leaf : Fin 4),
        rows[4 * side.val + leaf.val].toFinset =
          (canonicalRepresentationData I).zeroSetup.rawBackground (e, signs)
            ((canonicalRepresentationData I).zeroSetup.allocatedBackground (e, signs) g hn hlog)
            side leaf := by
  let R := (canonicalRepresentationData I).zeroSetup
  let V := Finset.univ \ R.mixerUnion (e, signs)
  let out := CanonicalBackground.run v
  let counts := (RepresentationAllocationExecution.run n guesses).1
  have hout : out.1 = V.sort (· ≤ ·) := CanonicalBackground.value I v e hv signs
  have hcard : V.card = out.1.length := by rw [hout, Finset.length_sort]
  have hc : (∑ i : Fin 8, counts[i.val]) = out.1.length := size_check I v e hv guesses g hg hn hlog
  let xs : Vector (Fin n) out.1.length := ⟨out.1.toArray, by simp only [List.size_toArray]⟩
  have hxs (k : Fin out.1.length) : xs[k.val] = ((V.orderIsoOfFin hcard) k).val := by
    rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
    change out.1[k.val] = _
    simp only [hout]
    rfl
  let rows := (StoredBackgroundBlocks.run xs counts hc).1
  refine ⟨rows, ?_, ?_⟩
  · exact run_of_size I v guesses hc
  · intro side leaf
    let index : Fin 8 := ⟨4 * side.val + leaf.val, by omega⟩
    have hrow := StoredBackgroundBlocks.row_source_of_size V hcard xs hxs counts hc index
    have hcounts : (fun i : Fin 8 => counts[i.val]) = representationLeafCounts n g := by
      funext i
      exact RepresentationAllocationExecution.value n guesses g hg i
    simp only [hcounts] at hrow
    dsimp only [rows, StoredBackgroundBlocks.run]
    rw [Vector.getElem_ofFn]
    change (StoredBackgroundBlocks.row xs counts hc index).toFinset = _
    rw [hrow]
    ext x
    simp only [V, R, RepresentationSetup.rawBackground, RepresentationSetup.allocatedBackground,
      backgroundPairColor_eq_iff]
    rfl

end LowSpaceSubsetSum.RepresentationBackgroundPreparation

end

end OAI
