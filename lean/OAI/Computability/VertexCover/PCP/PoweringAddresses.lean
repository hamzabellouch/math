import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringLabels

namespace OAI

                                                                                          

namespace UniqueGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

theorem length_allWords (d : Nat) :
    ∀ n, (allWords d n).length = d ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allWords, List.length_flatMap, List.length_map, ih,
      List.map_const', List.length_finRange, List.sum_replicate_nat]
    exact (Nat.mul_comm d (d ^ n)).trans (Nat.pow_succ d n).symm

theorem length_allAddresses (d t : Nat) :
    (allAddresses d t).length = ∑ n : Fin (t + 1), d ^ n.val := by
  unfold allAddresses
  simp only [List.length_flatMap, List.length_map, length_allWords]
  exact (Fin.sum_univ_def (fun n : Fin (t + 1) => d ^ n.val)).symm

def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end UniqueGames.Foundations.PCP.PoweringAddresses

end OAI
