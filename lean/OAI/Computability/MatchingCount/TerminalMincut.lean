import OAI.Computability.MatchingCount.UnitMincut

namespace OAI

section

namespace BinaryMatching.TerminalMincut
open Finset UnitFlow UnitMincut
variable {n : ℕ}

def Separates (U S : Finset (Fin n)) : Prop :=
  ∃ a∈U, ∃ z∈U, a∈S ∧ z∉S

def pairCuts (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : List (Finset (Fin n)) :=
  (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)

def terminalCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  ((pairCuts c U).argmin (cutCapacity c)).getD ∅

lemma mem_pairCuts (c : Fin n → Fin n → ℕ) (U S : Finset (Fin n)) :
    S∈pairCuts c U ↔ ∃ a∈U, ∃ z∈U, a≠z ∧ S=mincut c a z := by
  simp only [pairCuts,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,z⟩,⟨_,ha,hz,haz⟩,hS⟩
    exact ⟨a,ha,z,hz,haz,hS.symm⟩
  · rintro ⟨a,ha,z,hz,haz,hS⟩
    exact ⟨(a,z),⟨by simp,ha,hz,haz⟩,hS.symm⟩

lemma pairCuts_nonempty (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    pairCuts c U ≠ [] := by
  obtain ⟨a,ha,z,hz,haz⟩ := Finset.one_lt_card.mp hU
  have hm := (mem_pairCuts c U (mincut c a z)).2 ⟨a,ha,z,hz,haz,rfl⟩
  intro hh
  simp [hh] at hm

lemma terminalCut_mem (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    terminalCut c U∈(pairCuts c U).argmin (cutCapacity c) := by
  have hn := pairCuts_nonempty c U hU
  unfold terminalCut
  cases he : (pairCuts c U).argmin (cutCapacity c) with
  | none => exact (hn (List.argmin_eq_none.mp he)).elim
  | some S => simp

lemma terminalCut_correct (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    Separates U (terminalCut c U) ∧
      ∀ T : Finset (Fin n), Separates U T → cutCapacity c (terminalCut c U) ≤ cutCapacity c T := by
  have hmem := terminalCut_mem c U hU
  obtain ⟨a,ha,z,hz,haz,heq⟩ := (mem_pairCuts c U _).1 (List.argmin_mem hmem)
  constructor
  · obtain ⟨hac,hzc,_⟩ := mincut_correct c a z haz
    exact ⟨a,ha,z,hz,heq.symm ▸ hac,heq.symm ▸ hzc⟩
  · intro T hT
    obtain ⟨u,hu,v,hv,huT,hvT⟩ := hT
    have huv : u≠v := by intro hh; subst v; exact hvT huT
    have hpair := (mem_pairCuts c U (mincut c u v)).2 ⟨u,hu,v,hv,huv,rfl⟩
    exact (List.le_of_mem_argmin hpair hmem).trans ((mincut_correct c u v huv).2.2 T huT hvT)

end BinaryMatching.TerminalMincut
end

end OAI
