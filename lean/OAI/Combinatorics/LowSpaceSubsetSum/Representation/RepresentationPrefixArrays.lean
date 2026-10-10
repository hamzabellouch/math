import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLayoutPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPartitions

namespace OAI

/-! # The stored layout, guesses and balanced partitions of one trial

All three stages stop on exhaustion. The dependent seed's ideal layout is
used only as a type index for the partition sampler, whose actual code is
the fixed sequence of bounded integer draws and array scans.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPrefixArrays

variable {n : ℕ}

structure Data (n : ℕ) where
  layout : RepresentationLayoutPreparation.Data n
  guesses : Vector ℕ 3
  partitions : StoredPartitions.Data n

def run (D : RepresentationData n) (s : D.zeroSetup.partitionHistoryCoupling.Seed) :
    Option (Data n) × ℕ :=
  let layout := RepresentationLayoutPreparation.run D s.1.1
  match layout.1 with
  | none => (none, layout.2 + 1)
  | some l =>
    let guesses := GuessArrayExecution.run n s.1.2
    match guesses.1 with
    | none => (none, layout.2 + guesses.2 + 2)
    | some g =>
      let partitions := StoredPartitions.run D.zeroSetup (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2
      (partitions.1.map (fun p => ⟨l, g, p⟩), layout.2 + guesses.2 + partitions.2 + 3)

theorem layout_none_iff (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed) :
    (RepresentationLayoutPreparation.run D s).1 = none ↔
      D.zeroSetup.layoutCoupling.bounded s = none := by
  cases hs : D.zeroSetup.layoutCoupling.bounded s with
  | none =>
    constructor
    · intro _; rfl
    · intro _
      cases hr : (RepresentationLayoutPreparation.run D s).1 with
      | none => rfl
      | some data =>
        obtain ⟨e, he, _⟩ := RepresentationLayoutPreparation.value D s data hr
        rw [hs] at he
        contradiction
  | some z =>
    obtain ⟨data, hd, _⟩ := RepresentationLayoutPreparation.complete D s z.1 z.2 hs
    simp only [hd, reduceCtorEq]

theorem none_iff (D : RepresentationData n) (s : D.zeroSetup.partitionHistoryCoupling.Seed) :
    (run D s).1 = none ↔ D.zeroSetup.partitionHistoryCoupling.bounded s = none := by
  have hl := layout_none_iff D s.1.1
  have hg : (GuessArrayExecution.run n s.1.2).1 = none ↔
      D.zeroSetup.guessesCoupling.bounded s.1.2 = none := by
    exact (Iff.of_eq (congrArg (fun x => x = none)
      (GuessArrayExecution.value n s.1.2))).trans Option.map_eq_none_iff
  have hp : (StoredPartitions.run D.zeroSetup
      (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2).1 = none ↔
      (D.zeroSetup.partitionsCoupling (D.zeroSetup.layoutCoupling.ideal s.1.1)).bounded s.2 = none := by
    exact (Iff.of_eq (congrArg (fun x => x = none)
      (StoredPartitions.value D.zeroSetup (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2))).trans
      Option.map_eq_none_iff
  have hsource : D.zeroSetup.partitionHistoryCoupling.bounded s = none ↔
      D.zeroSetup.layoutCoupling.bounded s.1.1 = none ∨
      D.zeroSetup.guessesCoupling.bounded s.1.2 = none ∨
      (D.zeroSetup.partitionsCoupling (D.zeroSetup.layoutCoupling.ideal s.1.1)).bounded s.2 = none := by
    simp only [RepresentationSetup.partitionHistoryCoupling, RepresentationSetup.guessHistoryCoupling,
      SamplerCoupling.bind]
    split <;> split <;> simp_all
  rw [hsource, ← hl, ← hg, ← hp]
  cases hL : (RepresentationLayoutPreparation.run D s.1.1).1 <;>
    cases hG : (GuessArrayExecution.run n s.1.2).1 <;>
    cases hP : (StoredPartitions.run D.zeroSetup
      (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2).1 <;>
    simp only [run, hL, hG, hP, reduceCtorEq, Option.map_none, Option.map_some,
      or_true, or_false]

theorem complete (D : RepresentationData n) (s : D.zeroSetup.partitionHistoryCoupling.Seed)
    (h : D.zeroSetup.PartitionHistory)
    (hs : D.zeroSetup.partitionHistoryCoupling.bounded s = some h) :
    ∃ data, (run D s).1 = some data := by
  cases hr : (run D s).1 with
  | none =>
    have hf := (none_iff D s).mp hr
    rw [hs] at hf
    contradiction
  | some data => exact ⟨data, rfl⟩

theorem components (D : RepresentationData n) (s : D.zeroSetup.partitionHistoryCoupling.Seed)
    (data : Data n) (h : (run D s).1 = some data) :
    (RepresentationLayoutPreparation.run D s.1.1).1 = some data.layout ∧
      (GuessArrayExecution.run n s.1.2).1 = some data.guesses ∧
      (StoredPartitions.run D.zeroSetup (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2).1 =
        some data.partitions := by
  unfold run at h
  cases hL : (RepresentationLayoutPreparation.run D s.1.1).1 with
  | none => simp only [hL, reduceCtorEq] at h
  | some l =>
    simp only [hL] at h
    cases hG : (GuessArrayExecution.run n s.1.2).1 with
    | none => simp only [hG, reduceCtorEq] at h
    | some g =>
      simp only [hG] at h
      obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      subst data
      exact ⟨rfl, rfl, hp⟩

theorem work (D : RepresentationData n) (hn : 10000 ≤ n)
    (s : D.zeroSetup.partitionHistoryCoupling.Seed) :
    (run D s).2 ≤ n * n ^ 3 + 10 * (n + 1) ^ 2 + 4 * n + 6 +
      inputScale D.input ^ 6 * 2 ^ mixerSize n + 3 * n ^ 3 +
      3 * (mixerSize n * n ^ 3 + 10 * (mixerSize n + 1) ^ 2 + 4 * mixerSize n + 6) + 11 := by
  have hl := RepresentationLayoutPreparation.work D hn s.1.1
  have hg := GuessArrayExecution.work n s.1.2
  have hp := StoredPartitions.work D.zeroSetup (D.zeroSetup.layoutCoupling.ideal s.1.1) s.2
  unfold run
  dsimp only
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

end LowSpaceSubsetSum.RepresentationPrefixArrays

end

end OAI
