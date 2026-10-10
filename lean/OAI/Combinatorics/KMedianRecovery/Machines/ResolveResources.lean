import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CopyAge
import OAI.Combinatorics.KMedianRecovery.Machines.CoupledLoop
import OAI.Combinatorics.KMedianRecovery.Machines.MergeResources
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthHeight

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer RationalLeaves RationalHeight CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

lemma banks_bound {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) :
    BankBound F h (3*q+2) (q*(2*F.card+1)+2*F.card) (banks F s.mapFree q) := by
  have hh := hs.map_bound.pool.pool
  dsimp only [banks]
  convert hh using 1; omega

lemma resolve_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k H p : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V))
    (hb : BankBound F (CanonicalLengthSearch.heightBudget (20*N*M) precision H)
      (3*q+2) (q*(2*F.card+1)+2*F.card) B)
    (hlam : Height lam p) (hfar : Height (20*N*M) H) :
    (resolve loc distance F v M N precision q n k (3*q+2) B lam P R).Resources F q
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  let h := CanonicalLengthSearch.heightBudget (20*N*M) precision H
  have hsize : q*(2*F.card+1)+2*F.card+1=(q+1)*(2*F.card+1) := by ring
  have hmono : BankBound F h (3*(q+1)) ((q+1)*(2*F.card+1)) B :=
    hb.mono (by omega) (by omega)
  cases R with
  | success G T=>exact ⟨hmono,hlam⟩
  | common G T U=>exact ⟨hmono,True.intro,hlam,hlam⟩
  | sensitive G J T U=>
    dsimp only [resolve]
    cases hv : view (rows distance) (F.image original) ((F.sort (·≤·)).map original) G J with
    | none=>exact ⟨hmono,hlam⟩
    | some plan=>
      dsimp only
      have ha:=view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) G J plan hv
      have hroot : plan.root∈F.image original := by
        cases plan <;> exact ha.1
      have hparent : parent plan.root∈F := by
        obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hroot
        rw [←he]
        exact hi
      have hh := CanonicalSensitiveEndpoint.run_height loc distance F (after ∅ P) v lam (20*N*M)
        q n k (3*q+2) precision H G T U plan hfar
      cases he : CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M)
          q n k (3*q+2) precision G T U plan with
      | success s W=>
        rw [he] at hh
        refine ⟨?_,hlam⟩
        have ht := hb.insert (parent plan.root) hparent s hh
        rw [hsize] at ht
        convert ht using 1; rfl
      | bracket l u A Z=>
        rw [he] at hh
        refine ⟨?_,hh,hlam,hlam⟩
        have ht := hb.insert (parent plan.root) hparent u hh.2
        rw [hsize] at ht
        convert ht using 1; rfl

lemma step_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k H p : ℕ) (s : State V)
    (hs : s.Resources F q (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p)
    (hfar : Height (20*N*M) H) :
    (step loc distance F v M N precision q n k s).Resources F q
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  dsimp only [step]
  split
  · split_ifs
    · exact ⟨hs.map_bound.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.newPrice⟩
    · exact resolve_resources loc distance F v M N precision q n k H p _ _ _ _ (banks_bound hs) hs.newPrice hfar
    · exact hs.advance _ _ _
  · exact ⟨hs.bank.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.oldPrice⟩

lemma run_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision k H p : ℕ) (hfar : Height (20*N*M) H)
    (q n : ℕ) (s : State V)
    (hs : s.Resources F q (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p) :
    (run loc distance F v M N precision k q n s).Resources F (q+n)
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  induction n generalizing q s with
  | zero=>exact ⟨hs.bank,hs.oldPrice⟩
  | succ n ih=>
    have ht:=step_resources loc distance F v M N precision q n k H p s hs hfar
    rw [run]
    cases he : step loc distance F v M N precision q n k s with
    | inl o=>
      rw [he] at ht
      exact ht.mono (by omega)
    | inr t=>
      rw [he] at ht
      have hh:=ih (q+1) t ht
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 n] using hh

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
