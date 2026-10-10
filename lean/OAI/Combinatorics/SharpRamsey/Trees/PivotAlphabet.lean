import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotExecution

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev FirstSize := Fin (Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V)))+1)
abbrev SecondSize := Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)

def firstBound (b : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (t : ℕ) : ℕ :=
  scheduleCutoff (Nat.card K) (b+log 1000000) (scheduleLength (Nat.card K) U.2.card t)

def secondBound (b : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (s : ℕ) : ℕ :=
  scheduleCutoff (Nat.card K) (b+log 1000000)
    (scheduleLength (Nat.card K) (U.1.image (bidual (K:=K) (V:=V))).card s)

variable {n : ℕ} {b τ P H : ℝ}
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

abbrev Book.LocalRaw
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :=
  Σ s : FirstSize (K:=K) (V:=V), Σ t : SecondSize (K:=K) (V:=V),
    (book.library U s t) × Fin (firstBound b U t) × Fin (secondBound b U s)

def Book.decodeRaw (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (v : book.LocalRaw U) : Option (Code (K:=K) (V:=V) b) :=
  if hW : v.2.2.1.val.Nonempty then
    let a : Address (Projectivization K V) (Projectivization K (Module.Dual K V)) :=
      (⟨v.2.2.1.val,hW⟩,U.2,v.2.1)
    let i : Fin (cutoff (Nat.card K) (b+log 1000000) a) := v.2.2.2.1
    let B := cap SharpLogRamsey.Incidence.Incident (Nat.card K) U.2 (rowAt _ (z a) i)
    if hB : B.Nonempty then
      let a' : Address (Projectivization K (Module.Dual K V))
          (Projectivization K (Module.Dual K (Module.Dual K V))) :=
        (⟨B,hB⟩,U.1.image (bidual (K:=K) (V:=V)),v.1)
      let j : Fin (cutoff (Nat.card K) (b+log 1000000) a') := v.2.2.2.2
      some (⟨a,i⟩,⟨a',j⟩)
    else none
  else none

def Book.allowed (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    Finset (Code (K:=K) (V:=V) b) :=
  univ.biUnion (fun v : book.LocalRaw U=>(book.decodeRaw z U v).toFinset)

omit [Finite K] in
lemma Book.mem_allowed (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (v : book.LocalRaw U) (c : Code (K:=K) (V:=V) b) (hc : book.decodeRaw z U v=some c) :
    c∈book.allowed z U := by
  refine mem_biUnion.mpr ⟨v,mem_univ _,?_⟩
  rw [hc]
  exact mem_singleton_self c

omit [Finite K] in
lemma Book.allowed_card (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    (book.allowed z U).card≤
      ∑ s : FirstSize (K:=K) (V:=V),∑ t : SecondSize (K:=K) (V:=V),
        (book.library U s t).card*firstBound b U t*secondBound b U s := by
  have hh : (book.allowed z U).card≤Fintype.card (book.LocalRaw U) := by
    apply (card_biUnion_le).trans
    calc
      _ ≤ ∑ _v : book.LocalRaw U,1 := by
        apply sum_le_sum
        intro v _
        cases book.decodeRaw z U v <;> simp
      _ = _ := by simp
  simpa only [Book.LocalRaw,Fintype.card_sigma,Fintype.card_prod,
    Fintype.card_coe,Fintype.card_fin,←Nat.mul_assoc] using hh

end
end SharpLogRamsey.ActualPivot

end

end OAI
