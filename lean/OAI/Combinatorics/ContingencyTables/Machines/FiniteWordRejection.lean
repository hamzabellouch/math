import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw

namespace OAI

/-! # Repeated rejection implemented by one finite independent Boolean array -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

theorem retryLaw_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (p : RationalLaw A) (draw : A → B) (f : B → Option C) (fallback : C) (n : ℕ) :
    retryLaw (mapLaw p draw) f fallback n = retryLaw p (fun x => f (draw x)) fallback n := by
  have hm := mapLaw_comp p draw f
  have hg : successMass (mapLaw p draw) f = successMass p (fun x => f (draw x)) := by
    funext z
    exact congrArg (fun q : RationalLaw (Option C) => q.mass (some z)) hm
  have hf : failureMass (mapLaw p draw) f = failureMass p (fun x => f (draw x)) :=
    congrArg (fun q : RationalLaw (Option C) => q.mass none) hm
  apply RationalLaw.ext
  funext z
  simp only [retryLaw_mass, hg, hf]

variable {α : Type*} [Fintype α] [DecidableEq α]

def wordRetry {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) :
    (n : ℕ) → (Fin n → Fin k → Bool) → α
  | 0, _ => fallback
  | n + 1, bits => (f (bits 0)).getD (wordRetry f fallback n (Fin.tail bits))

def wordRetryLaw {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) (n : ℕ) : RationalLaw α :=
  mapLaw (uniformLaw (α := Fin n → Fin k → Bool)) (wordRetry f fallback n)

/-- The first successful output is computed from an actual fixed Boolean
array; unused suffix words do not change its distribution. -/
theorem wordRetryLaw_eq {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) (n : ℕ) :
    wordRetryLaw f fallback n = retryLaw (uniformLaw (α := Fin k → Bool)) f fallback n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext z
    simp [wordRetryLaw, wordRetry, retryLaw, pointLaw, mapLaw, uniformLaw, uniformMass, eq_comm]
  | succ n ih =>
    let E : ((Fin k → Bool) × (Fin n → Fin k → Bool)) ≃ (Fin (n + 1) → Fin k → Bool) :=
      Fin.consEquiv (fun _ => Fin k → Bool)
    have hc : (fun z => wordRetry f fallback (n + 1) (E z)) =
        fun z => (f z.1).getD (wordRetry f fallback n z.2) := by
      funext z
      rcases z with ⟨head, tail⟩
      change (f ((Fin.cons (α := fun _ : Fin (n+1) => Fin k → Bool) head tail) 0)).getD
        (wordRetry f fallback n (Fin.tail (Fin.cons (α := fun _ : Fin (n+1) => Fin k → Bool) head tail))) = _
      simp only [Fin.cons_zero, Fin.tail_cons]
    unfold wordRetryLaw
    rw [← uniform_equiv E, map_equiv E, hc, ← uniform_product]
    have hcomp := mapLaw_comp
      (productLaw (uniformLaw (α := Fin k → Bool)) (uniformLaw (α := Fin n → Fin k → Bool)))
      (fun z => (id z.1, wordRetry f fallback n z.2)) (fun z => (f z.1).getD z.2)
    dsimp only [id_eq, Prod.fst, Prod.snd] at hcomp
    rw [← hcomp]
    have hp := mapLaw_product (uniformLaw (α := Fin k → Bool))
      (uniformLaw (α := Fin n → Fin k → Bool)) id (wordRetry f fallback n)
    dsimp only [id_eq] at hp
    rw [hp, mapLaw_id]
    change retryStep (uniformLaw (α := Fin k → Bool)) f (wordRetryLaw f fallback n) = _
    rw [ih]
    rfl

end

end ContingencyTables.FirstSuccess

end OAI
