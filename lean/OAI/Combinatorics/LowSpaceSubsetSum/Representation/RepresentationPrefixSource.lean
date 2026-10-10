import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrefixArrays

namespace OAI

/-! # Identifying every stored prefix field with its bounded history

The witness is the coupling's ideal history, but only after the concrete
prefix has succeeded. The coupling agreement proof then identifies it with
the returned bounded history; no backup is used by the execution.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPrefixArrays

variable {n : ℕ}

theorem source (D : RepresentationData n) (s : D.zeroSetup.partitionHistoryCoupling.Seed)
    (data : Data n) (h : (run D s).1 = some data) :
    ∃ history : D.zeroSetup.PartitionHistory,
      D.zeroSetup.partitionHistoryCoupling.bounded s = some history ∧
      data.layout.signs.semantic = history.1.1.2 ∧
      (∀ i : Fin n, data.layout.permutation[i.val] = history.1.1.1 i) ∧
      (∀ j : Fin 3, data.guesses[j.val] = (history.1.2 j).val) ∧
      (∀ (j : Fin 3) (k : Fin (PartitionLabelExecution.size n j)),
        (data.partitions j)[k.val] =
          (history.2 j).val ((CanonicalPartition.ranks D.zeroSetup history.1.1 j).symm k)) ∧
      (∀ j : Fin 4, data.layout.parameters.widths[j.val] =
        D.zeroSetup.samplerPrimeWidths history.1.1 j) := by
  let z := D.zeroSetup.layoutCoupling.ideal s.1.1
  let g := D.zeroSetup.guessesCoupling.ideal s.1.2
  let f := (D.zeroSetup.partitionsCoupling z).ideal s.2
  let history : D.zeroSetup.PartitionHistory := ⟨⟨z, g⟩, f⟩
  have hb : D.zeroSetup.partitionHistoryCoupling.bounded s = some history := by
    rcases D.zeroSetup.partitionHistoryCoupling.agrees s with hn | he
    · have hf := (none_iff D s).mpr hn
      rw [h] at hf
      contradiction
    · exact he
  obtain ⟨hl, hg, hp⟩ := components D s data h
  obtain ⟨e, he, hv, _, hw⟩ := RepresentationLayoutPreparation.value D s.1.1 data.layout hl
  have hz : z = (e, data.layout.signs.semantic) :=
    D.zeroSetup.layoutExecution.ideal_eq_of_some s.1.1 _
      ((D.zeroSetup.layoutExecution.value_eq s.1.1).trans he)
  have hguess := (GuessArrayExecution.value n s.1.2).symm.trans hg
  obtain ⟨drawn, hd, hdv⟩ := Option.map_eq_some_iff.mp hguess
  have hgi : g = drawn :=
    D.zeroSetup.guessesExecution.ideal_eq_of_some s.1.2 _
      ((D.zeroSetup.guessesExecution.value_eq s.1.2).trans hd)
  obtain ⟨drawnParts, hdp, hpart⟩ :=
    StoredPartitions.source D.zeroSetup z s.2 data.partitions hp
  have hfi : f = drawnParts :=
    (D.zeroSetup.partitionsExecution z).ideal_eq_of_some s.2 _
      (((D.zeroSetup.partitionsExecution z).value_eq s.2).trans hdp)
  refine ⟨history, hb, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Prod.snd hz).symm
  · intro i
    exact (hv i).trans (congrArg (fun q : RepresentationSetup.Layout n => q.1 i) hz).symm
  · intro j
    change data.guesses[j.val] = (g j).val
    rw [hgi]
    simpa only [Vector.getElem_ofFn, Fin.eta] using
      (congrArg (fun v : Vector ℕ 3 => v[j.val]) hdv).symm
  · intro j k
    change (data.partitions j)[k.val] = (f j).val ((CanonicalPartition.ranks D.zeroSetup z j).symm k)
    rw [hfi]
    exact hpart j k
  · intro j
    change data.layout.parameters.widths[j.val] = D.zeroSetup.samplerPrimeWidths z j
    rw [hz]
    exact hw j

end LowSpaceSubsetSum.RepresentationPrefixArrays

end

end OAI
