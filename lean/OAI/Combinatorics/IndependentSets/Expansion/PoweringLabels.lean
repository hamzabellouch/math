import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringWalks

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

theorem card_portWords [Finite D] (t : Nat) :
    Nat.card (PortWords D t) = ∑ n : Fin (t + 1), Nat.card D ^ n.val := by
  simp [PortWords, Nat.card_sigma, Nat.card_fun]

theorem card_ball_le [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Nat.card (Ball G t v) ≤ ∑ n : Fin (t + 1), Nat.card D ^ n.val := by
  calc
    _ ≤ Nat.card (PortWords D t) := Nat.card_le_card_of_surjective
      (wordToBall G t v) (wordToBall_surjective G t v)
    _ = _ := card_portWords t

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

noncomputable def classicalSelector (G : PortGraph V D) (t : Nat) (v : V) :
    AddressSelector G t v where
  address u := Classical.choose (wordToBall_surjective G t v u)
  correct u := Classical.choose_spec (wordToBall_surjective G t v u)

def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

theorem decode_surjective {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) : Function.Surjective (decode (A := A) S) :=
  fun ℓ => ⟨encode G t v ℓ, decode_encode S ℓ⟩

theorem encode_injective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Injective (encode (A := A) G t v) := by
  intro a b h
  funext u
  obtain ⟨w, rfl⟩ := wordToBall_surjective G t v u
  exact congrFun h w

theorem decoded_word_collision {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (a : PaddedLabel D t A) (w z : PortWords D t)
    (h : (wordToBall G t v w).val = (wordToBall G t v z).val) :
    decode S a (wordToBall G t v w) = decode S a (wordToBall G t v z) :=
  congrArg (decode S a) (Subtype.ext h)

theorem card_paddedLabel [Finite D] [Finite A] (t : Nat) :
    Nat.card (PaddedLabel D t A) =
      Nat.card A ^ (∑ n : Fin (t + 1), Nat.card D ^ n.val) := by
  rw [Nat.card_fun, card_portWords]

end IndependentSetsGames.Foundations.PCP.PoweringLabels
namespace IndependentSetsGames.Foundations.PCP.PoweringAddresses

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

end IndependentSetsGames.Foundations.PCP.PoweringAddresses

end OAI
