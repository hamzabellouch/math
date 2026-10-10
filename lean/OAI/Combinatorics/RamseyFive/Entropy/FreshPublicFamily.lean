import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FinitePiLaw
import OAI.Combinatorics.RamseyFive.Probability.AmbientPublicTest

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma exists_accepted_index {n : ℕ} (E : Finset A) (t : Fin n→A) :
    ∃i : Option (Fin n),Option.map t i=firstAccepted E t := by
  cases he : firstAccepted E t with
  | none => exact ⟨none,rfl⟩
  | some a =>
    obtain ⟨i,hi,_⟩ := firstAccepted_index E t he
    exact ⟨some i,by simpa only [Option.map_some] using congrArg some hi⟩

noncomputable def acceptedIndex {n : ℕ} (E : Finset A) (t : Fin n→A) : Option (Fin n) :=
  Classical.choose (exists_accepted_index E t)
lemma acceptedIndex_decode {n : ℕ} (E : Finset A) (t : Fin n→A) :
    Option.map t (acceptedIndex E t)=firstAccepted E t :=
  Classical.choose_spec (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def cardCutoff (q : ℝ) (m w n : ℕ) : ℕ :=
  ⌈q/((9:ℝ)/10*((m:ℝ)/w)^n)⌉₊

abbrev FreshTape (W : Finset B) (n : ℕ) (q : ℝ) :=
  (m : Fin (W.card+1))→Fin (cardCutoff q m W.card n)→Fin n→B

noncomputable def freshTapeLaw (W : Finset B) (hW : W.Nonempty) (n : ℕ) (q : ℝ) :
    Law (FreshTape W n q) :=
  piLaw fun m : Fin (W.card+1)=>iid (iid (uniformOn W hW) (Fin n)) (Fin (cardCutoff q m W.card n))

abbrev FreshMessage (W : Finset B) (n : ℕ) (q : ℝ) :=
  (m : Fin (W.card+1))×Fin (cardCutoff q m W.card n)

noncomputable def freshDecoded (R : A→B→Prop) (W : Finset B) (n : ℕ) (q : ℝ)
    (t : FreshTape W n q) (m : FreshMessage W n q) : Finset A :=
  cap R Finset.univ q (t m.1 m.2)

noncomputable def freshEncoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option (FreshMessage W n q) :=
  let m : Fin (W.card+1) := ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩
  Option.map (fun i=>⟨m,i⟩) (acceptedIndex (validationRows R S U C n q M) (t m))

lemma freshEncoded_decoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)=
      Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M)
          (t ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩)) := by
  unfold freshEncoded freshDecoded
  rw [←acceptedIndex_decode]
  simp only [Option.map_map]
  rfl

theorem fresh_public_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    map (freshTapeLaw W hW n q)
      (fun t=>Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t))=
    ambientCapLaw R S U C W hW n q M := by
  let m : Fin (W.card+1) := ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩
  have hm := piLaw_eval (fun m : Fin (W.card+1)=>
    iid (iid (uniformOn W hW) (Fin n)) (Fin (cardCutoff q m W.card n))) m
  have ht := congrArg (fun p=>map (map p (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R Finset.univ q))) hm
  simp only [map_comp] at ht
  unfold ambientCapLaw
  rw [map_comp]
  calc
    _ = map (freshTapeLaw W hW n q) (fun t=>Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M) (t m))) := by
      congr 1
      funext t
      exact freshEncoded_decoded R S U C W hCW n q M t
    _ = _ := ht

omit [Fintype B] in
theorem fresh_payload_cost (q : ℝ) (hq : 1≤q) (C W : Finset B)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ) :
    Real.log (Fintype.card (Fin (cardCutoff q C.card W.card n)):ℝ)≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+n*Real.log ((W.card:ℝ)/C.card) := by
  rw [Fintype.card_fin]
  simpa only [cardCutoff,uniformCutoff] using
    uniformCutoff_log q hq C W hC hW hCW n
end SharpRamseyFive.ReverseCap

end OAI
