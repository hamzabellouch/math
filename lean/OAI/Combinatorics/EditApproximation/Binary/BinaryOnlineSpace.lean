import OAI.Combinatorics.EditApproximation.Binary.BinaryBandStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The online objective includes every repeated history-buffer read.
Its allocation and frame counters follow the same Boolean arithmetic and
materialized vector passes as the executed continuation. -/

namespace EditApproximation.BinaryFraction



theorem coefficientAllocation_le_work (kappa : BinaryFraction) :
    coefficientAllocation kappa ≤ (coefficientWithWork kappa).2 := by
  have h1 := canonicalMulAllocation_le_work (nat 2) kappa
  have h2 := subAllocation_le_work one (canonicalMulWithWork (nat 2) kappa).1
  unfold coefficientAllocation coefficientWithWork
  dsimp only
  omega



theorem gainReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2) :
    gainReadAllocation mass read footprint s i ≤ (gainReadWithWork mass read s i).2 := by
  have hd := divAllocation_le_work (read s i).1.neg (mass i.1)
  unfold gainReadAllocation gainReadWithWork
  dsimp only
  omega



theorem decrementReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2)
    (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    decrementReadAllocation mass read footprint s i ≤ (decrementReadWithWork mass read s i).2 := by
  have hs := subAllocation_le_work (read s i).1 (read (s + 1) i).1
  have hd := divAllocation_le_work (subWithWork (read s i).1 (read (s + 1) i).1).1 (mass i.1)
  unfold decrementReadAllocation decrementReadWithWork
  dsimp only
  omega



theorem optimisticTermReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (coefficient : BinaryFraction) (s : ℕ) (i : β × σ)
    (h : footprint s i ≤ (read s i).2) (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    optimisticTermReadAllocation mass read footprint coefficient s i ≤
      (optimisticTermReadWithWork mass read coefficient s i).2 := by
  have hg := gainReadAllocation_le_work mass read footprint s i h
  have hd := decrementReadAllocation_le_work mass read footprint s i h hnext
  have hm := canonicalMulAllocation_le_work coefficient (decrementReadWithWork mass read s i).1
  have ha := canonicalAddAllocation_le_work (gainReadWithWork mass read s i).1
    (canonicalMulWithWork coefficient (decrementReadWithWork mass read s i).1).1
  unfold optimisticTermReadAllocation optimisticTermReadWithWork
  dsimp only
  omega



theorem onlineLinearReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (eta kappa : BinaryFraction) (t : ℕ) (i : β × σ)
    (h : ∀ s ≤ t + 1, footprint s i ≤ (read s i).2) :
    onlineLinearReadAllocation mass read footprint eta kappa t i ≤
      (onlineLinearReadWithWork mass read eta kappa t i).2 := by
  have hc := coefficientAllocation_le_work kappa
  have ht := vectorMapAllocation_le_work t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadAllocation mass read footprint (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadAllocation_le_work mass read footprint _ s.val i
      (h _ (by omega)) (h _ (by omega)))
  let terms := (vectorMapWithWork t fun s =>
    optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i).1
  have hh := bandMassAllocation_le_work terms
  have hg := gainReadAllocation_le_work mass read footprint t i (h _ (by omega))
  have ha := canonicalAddAllocation_le_work (bandMassTotalWithWork terms).1 (gainReadWithWork mass read t i).1
  have hm := canonicalMulAllocation_le_work eta (canonicalAddWithWork (bandMassTotalWithWork terms).1
    (gainReadWithWork mass read t i).1).1
  unfold onlineLinearReadAllocation onlineLinearReadWithWork
  dsimp only
  dsimp only [terms] at hh ha hm
  omega

def coefficientInvocations (kappa : BinaryFraction) : ℕ :=
  canonicalMulInvocations (nat 2) kappa + subInvocations one (canonicalMulWithWork (nat 2) kappa).1 + 1

theorem coefficientInvocations_le_work (kappa : BinaryFraction) :
    coefficientInvocations kappa ≤ (coefficientWithWork kappa).2 := by
  have h1 := canonicalMulInvocations_le_work (nat 2) kappa
  have h2 := subInvocations_le_work one (canonicalMulWithWork (nat 2) kappa).1
  unfold coefficientInvocations coefficientWithWork
  dsimp only
  omega

def gainReadInvocations {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) : ℕ :=
  footprint s i + divInvocations (read s i).1.neg (mass i.1) + 1

theorem gainReadInvocations_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2) :
    gainReadInvocations mass read footprint s i ≤ (gainReadWithWork mass read s i).2 := by
  have hd := divInvocations_le_work (read s i).1.neg (mass i.1)
  unfold gainReadInvocations gainReadWithWork
  dsimp only
  omega

def decrementReadInvocations {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) : ℕ :=
  footprint s i + footprint (s + 1) i + subInvocations (read s i).1 (read (s + 1) i).1 +
    divInvocations (subWithWork (read s i).1 (read (s + 1) i).1).1 (mass i.1) + 1

theorem decrementReadInvocations_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2)
    (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    decrementReadInvocations mass read footprint s i ≤ (decrementReadWithWork mass read s i).2 := by
  have hs := subInvocations_le_work (read s i).1 (read (s + 1) i).1
  have hd := divInvocations_le_work (subWithWork (read s i).1 (read (s + 1) i).1).1 (mass i.1)
  unfold decrementReadInvocations decrementReadWithWork
  dsimp only
  omega

def optimisticTermReadInvocations {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (coefficient : BinaryFraction) (s : ℕ) (i : β × σ) : ℕ :=
  let gain := (gainReadWithWork mass read s i).1
  let decrement := (decrementReadWithWork mass read s i).1
  gainReadInvocations mass read footprint s i + decrementReadInvocations mass read footprint s i +
    canonicalMulInvocations coefficient decrement +
    canonicalAddInvocations gain (canonicalMulWithWork coefficient decrement).1 + 1

theorem optimisticTermReadInvocations_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (coefficient : BinaryFraction) (s : ℕ) (i : β × σ)
    (h : footprint s i ≤ (read s i).2) (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    optimisticTermReadInvocations mass read footprint coefficient s i ≤
      (optimisticTermReadWithWork mass read coefficient s i).2 := by
  have hg := gainReadInvocations_le_work mass read footprint s i h
  have hd := decrementReadInvocations_le_work mass read footprint s i h hnext
  have hm := canonicalMulInvocations_le_work coefficient (decrementReadWithWork mass read s i).1
  have ha := canonicalAddInvocations_le_work (gainReadWithWork mass read s i).1
    (canonicalMulWithWork coefficient (decrementReadWithWork mass read s i).1).1
  unfold optimisticTermReadInvocations optimisticTermReadWithWork
  dsimp only
  omega

def onlineLinearReadInvocations {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (eta kappa : BinaryFraction) (t : ℕ) (i : β × σ) : ℕ :=
  let coefficient := (coefficientWithWork kappa).1
  let terms := (vectorMapWithWork t fun s => optimisticTermReadWithWork mass read coefficient s.val i).1
  let history := (bandMassTotalWithWork terms).1
  let current := (gainReadWithWork mass read t i).1
  coefficientInvocations kappa +
    vectorMapInvocations t (fun s => optimisticTermReadInvocations mass read footprint coefficient s.val i) +
    bandMassInvocations terms + gainReadInvocations mass read footprint t i + canonicalAddInvocations history current +
    canonicalMulInvocations eta (canonicalAddWithWork history current).1 + 1

theorem onlineLinearReadInvocations_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (eta kappa : BinaryFraction) (t : ℕ) (i : β × σ)
    (h : ∀ s ≤ t + 1, footprint s i ≤ (read s i).2) :
    onlineLinearReadInvocations mass read footprint eta kappa t i ≤
      (onlineLinearReadWithWork mass read eta kappa t i).2 := by
  have hc := coefficientInvocations_le_work kappa
  have ht := vectorMapInvocations_le_work_add_one t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadInvocations mass read footprint (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadInvocations_le_work mass read footprint _ s.val i
      (h _ (by omega)) (h _ (by omega)))
  let terms := (vectorMapWithWork t fun s =>
    optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i).1
  have hh := bandMassInvocations_le_work terms
  have hg := gainReadInvocations_le_work mass read footprint t i (h _ (by omega))
  have ha := canonicalAddInvocations_le_work (bandMassTotalWithWork terms).1 (gainReadWithWork mass read t i).1
  have hm := canonicalMulInvocations_le_work eta (canonicalAddWithWork (bandMassTotalWithWork terms).1
    (gainReadWithWork mass read t i).1).1
  unfold onlineLinearReadInvocations onlineLinearReadWithWork
  dsimp only
  dsimp only [terms] at hh ha hm
  omega

def preparedOptimizerReadAllocation {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × σ → ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ) : ℕ :=
  let vertices := (bandVerticesWithWork coordinates mass band).1
  let linear := (vectorMapWithWork d fun i =>
    onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)).1
  bandVerticesAllocation coordinates mass band +
    vectorMapAllocation d (fun i => onlineLinearReadAllocation
      (fun j => mass.get j) read footprint eta kappa t (coordinates.get i)) +
    optimizerAllocation vertices linear G K

def preparedOptimizerReadInvocations {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × σ → ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ) : ℕ :=
  let vertices := (bandVerticesWithWork coordinates mass band).1
  let linear := (vectorMapWithWork d fun i =>
    onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)).1
  bandVerticesInvocations coordinates mass band +
    vectorMapInvocations d (fun i => onlineLinearReadInvocations
      (fun j => mass.get j) read footprint eta kappa t (coordinates.get i)) +
    optimizerInvocations vertices linear G K + 1

theorem preparedOptimizerReadAllocation_le_work {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × σ → ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ)
    (h : ∀ s ≤ t + 1, ∀ i, footprint s (coordinates.get i) ≤ (read s (coordinates.get i)).2) :
    preparedOptimizerReadAllocation coordinates mass read footprint eta kappa band G K t ≤
      (preparedBandOptimizerReadWithWork coordinates mass read eta kappa band G K t).2 := by
  have hv := bandVerticesAllocation_le_work coordinates mass band
  have hl := vectorMapAllocation_le_work d
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation (fun j => mass.get j) read footprint eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation_le_work _ _ _ _ _ _ _ (fun s hs => h s hs i))
  have ho := optimizerAllocation_le_work (bandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork d fun i =>
      onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)).1 G K
  unfold preparedOptimizerReadAllocation preparedBandOptimizerReadWithWork
  dsimp only
  omega

theorem preparedOptimizerReadInvocations_le_work_add_one {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × σ → ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ)
    (h : ∀ s ≤ t + 1, ∀ i, footprint s (coordinates.get i) ≤ (read s (coordinates.get i)).2) :
    preparedOptimizerReadInvocations coordinates mass read footprint eta kappa band G K t ≤
      (preparedBandOptimizerReadWithWork coordinates mass read eta kappa band G K t).2 + 1 := by
  have hv := bandVerticesInvocations_le_work_add_one coordinates mass band
  have hl := vectorMapInvocations_le_work_add_one d
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadInvocations (fun j => mass.get j) read footprint eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadInvocations_le_work _ _ _ _ _ _ _ (fun s hs => h s hs i))
  have ho := optimizerInvocations_le_work (bandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork d fun i =>
      onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)).1 G K
  unfold preparedOptimizerReadInvocations preparedBandOptimizerReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
