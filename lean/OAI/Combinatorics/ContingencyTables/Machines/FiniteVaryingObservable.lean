import OAI.Combinatorics.ContingencyTables.Machines.FiniteVaryingWordWalk
import OAI.Combinatorics.ContingencyTables.Machines.FiniteEncodedHistory

namespace OAI

/-! # Observable transport for independent words of varying widths -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FirstSuccess
open scoped Classical

noncomputable section

lemma uniformAverage_pi_snoc {N : ℕ} {Y : Fin (N+1) → Type*}
    [∀ i,Fintype (Y i)] (f : ((i : Fin (N+1)) → Y i) → ℝ) :
    uniformAverage f=uniformAverage (fun xy :
      ((i : Fin N) → Y i.castSucc) × Y (Fin.last N) => f (Fin.snoc xy.1 xy.2)) := by
  let E : (((i : Fin N) → Y i.castSucc) × Y (Fin.last N)) ≃
      ((i : Fin (N+1)) → Y i) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv Y)
  exact (uniformAverage_equiv E f).symm

/-- The encoded state type need not be finite. Equality of every actual
conditional call transfers the entire variable-width experiment. -/
theorem varyingWalk_sameLaw {C Z : Type*} (u v : ℕ → ℕ)
    (F : (i : ℕ) → C → (Fin (u i) → Bool) → C)
    (G : (i : ℕ) → Z → (Fin (v i) → Bool) → Z) (e : Z → C)
    (h : ∀ i z,SameLaw (F i (e z)) (fun bits => e (G i z bits)))
    (z : Z) (N : ℕ) :
    SameLaw (varyingWalk u F (e z) N) (fun bits => e (varyingWalk v G z N bits)) := by
  intro phi
  induction N generalizing phi with
  | zero => simp only [varyingWalk,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_pi_snoc,uniformAverage_pi_snoc]
    simp only [varyingWalk,Fin.init_snoc,Fin.snoc_last]
    rw [uniformAverage_prod,uniformAverage_prod]
    have hi := ih (fun c => uniformAverage (fun bits : Fin (u N) → Bool => phi (F N c bits)))
    refine hi.trans ?_
    apply congrArg uniformAverage
    funext pref
    exact h N (varyingWalk v G z N pref) phi

/-- Only stages actually visited need a conditional-law identification. -/
theorem varyingWalk_sameLaw_prefix {C Z : Type*} (u v : ℕ → ℕ)
    (F : (i : ℕ) → C → (Fin (u i) → Bool) → C)
    (G : (i : ℕ) → Z → (Fin (v i) → Bool) → Z) (e : Z → C)
    (z : Z) (N : ℕ)
    (h : ∀ i,i < N → ∀ s,SameLaw (F i (e s)) (fun bits => e (G i s bits))) :
    SameLaw (varyingWalk u F (e z) N) (fun bits => e (varyingWalk v G z N bits)) := by
  intro phi
  induction N generalizing phi with
  | zero => simp only [varyingWalk,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_pi_snoc,uniformAverage_pi_snoc]
    simp only [varyingWalk,Fin.init_snoc,Fin.snoc_last]
    rw [uniformAverage_prod,uniformAverage_prod]
    have hi := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self N)))
      (fun c => uniformAverage (fun bits : Fin (u N) → Bool => phi (F N c bits)))
    refine hi.trans ?_
    apply congrArg uniformAverage
    funext pref
    exact h N (Nat.lt_succ_self N) (varyingWalk v G z N pref) phi

end
end ContingencyTables.FiniteObservableTransport

end OAI
