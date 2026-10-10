import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.InverseCDF

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical
lemma select_rank {A : Type*} (d : A) (ws : List (A×ℕ)) (v : ℕ) :
    select d ws v=((rank (ws.map Prod.snd) v).bind (fun j=>(ws[j]?).map Prod.fst)).getD d := by
  induction ws generalizing v with
  | nil=>rfl
  | cons w ws ih=>
    simp only [List.map_cons,select,rank]
    split_ifs with h
    · rfl
    · rw [ih]
      cases rank (ws.map Prod.snd) (v-w.2) <;>
        simp only [Option.map_none,Option.bind_none,Option.map_some,Option.bind_some,List.getElem?_cons_succ]
lemma select_rank_default {A : Type*} (d : A) (ws : List (A×ℕ)) (v : ℕ) (h : (ws[0]?).map Prod.fst=some d) :
    ((ws[(rank (ws.map Prod.snd) v).getD 0]?).map Prod.fst).getD d=select d ws v := by
  rw [select_rank]
  cases rank (ws.map Prod.snd) v <;> simp only [Option.getD_none,Option.getD_some,Option.bind_none,Option.bind_some,h]
lemma select_rank_map {A B : Type*} (code : A→B) (fallback : B) (d : A) (ws : List (A×ℕ)) (v : ℕ)
    (h : (ws[0]?).map Prod.fst=some d) :
    (((ws[(rank (ws.map Prod.snd) v).getD 0]?).map (fun z=>code z.1)).getD fallback)=code (select d ws v) := by
  have hl (xs : List ℕ) (u j : ℕ) (hh : rank xs u=some j) : j<xs.length := by
    induction xs generalizing u j with
    | nil=>simp [rank] at hh
    | cons x xs ih=>
      simp only [rank] at hh
      split_ifs at hh with hu
      · cases Option.some.inj hh; simp
      · obtain ⟨a,ha,hj⟩:=Option.map_eq_some_iff.mp hh
        rw [←hj]
        have hh2:=ih _ _ ha
        simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hh2
  have he : ∃ t,ws[(rank (ws.map Prod.snd) v).getD 0]?=some t := by
    cases hr : rank (ws.map Prod.snd) v with
    | none=>
      simp only [Option.getD_none]
      obtain ⟨t,ht,_⟩:=Option.map_eq_some_iff.mp h
      exact ⟨t,ht⟩
    | some j=>
      simp only [Option.getD_some]
      exact ⟨ws[j]'(by simpa only [List.length_map] using hl _ _ _ hr),by simp⟩
  obtain ⟨t,ht⟩:=he
  have hh:=select_rank_default d ws v h
  rw [ht,Option.map_some,Option.getD_some] at hh
  rw [ht,Option.map_some,Option.getD_some,←hh]
end MetricKMedianRecovery.Dyadic.Canonical
namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
lemma lookup_draw {A : Type*} (code : A→List Bool) (p : A→ℚ) (d : A) (as : List A)
    (ha : as[0]?=some d) (b : ℕ) (s : Fin b→Bool) :
    Lookup.run (pairBits (run (pack b 0 (as.map p) (List.ofFn s)),encode (as.map code)))=
      code (Dyadic.Canonical.draw (fun a=>(p a:ℝ)) b d as s) := by
  rw [run_pack,Lookup.run_encode]
  have hh:=Dyadic.Canonical.select_rank_map code [] d (as.map (fun a=>(a,⌊p a*(2:ℚ)^b⌋₊)))
    (Categorical.uniformBits b s).val (by simp only [List.getElem?_map,ha,Option.map_some])
  simpa only [List.map_map,Function.comp_def,List.getElem?_map,Option.map_map,
    Dyadic.Canonical.draw,Dyadic.Canonical.list,rawCount_cast] using hh
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
