import OAI.Analysis.LipschitzFree.GraphGirth
import OAI.Analysis.LipschitzFree.GraphWalks
import OAI.Analysis.LipschitzFree.ColorCounting

namespace OAI

/-!
# Rare matched walks and the fixed all-colorings graph sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Fintype A] [DecidableEq A]
    (C S : Type*) [Fintype C] [Fintype S]

theorem rare_matched_bound (n N Q H : ℕ) (hnN : n ≤ N)
    (compatible : ((Cayley A N → C) × Cayley A N) → S → Prop)
    (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → z.1 z.2 ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    Nat.card {z : (Cayley A N → C) × Cayley A N //
        ¬ (allColoringsGraph A C N).Good compatible trans n z} * Nat.card C ^ (n+1) ≤
      Nat.card (A × Bool) ^ n * (Nat.card S * Q ^ n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := by
  let W := {w : Words (A × Bool) n // (cayleyGraph A N).Reduced w.val}
  let f : Cayley A N → W → Fin (n+1) → Cayley A N :=
    fun x w i => (cayleyGraph A N).walk x (w.val.val.take i.val)
  have hf : ∀ x w, Function.Injective (f x w) := by
    intro x w i j h
    have hi : i.val < w.val.val.length+1 := by rw [w.val.property]; exact i.isLt
    have hj : j.val < w.val.val.length+1 := by rw [w.val.property]; exact j.isLt
    have hw : w.val.val.length ≤ N := by rw [w.val.property]; exact hnN
    have hh := cayley_prefix_injective A N x w.val.val w.property hw
      (show (cayleyGraph A N).walk x (w.val.val.take (⟨i.val, hi⟩ : Fin (w.val.val.length+1)).val) =
        (cayleyGraph A N).walk x (w.val.val.take (⟨j.val, hj⟩ : Fin (w.val.val.length+1)).val) from h)
    exact Fin.ext (congrArg (fun t : Fin (w.val.val.length+1) => t.val) hh)
  let PC : StatePaths.Path trans n → Fin (n+1) → Finset C :=
    fun p i => P (StatePaths.Path.vertex trans p i)
  let B := {z : (Cayley A N → C) × Cayley A N //
    ¬ (allColoringsGraph A C N).Good compatible trans n z}
  let E := {z : (Cayley A N → C) × Cayley A N //
    ∃ w p, ∀ i, z.1 (f z.2 w i) ∈ PC p i}
  have hBE : Nat.card B ≤ Nat.card E := by
    let emb : B → E := fun z => ⟨z.val, by
      have hz := z.property
      simp only [PortGraph.Good, not_forall, not_not] at hz
      obtain ⟨j, w, hw, hr, hm⟩ := hz
      obtain ⟨p, hp⟩ := PortGraph.Matched.exists_based (allColoringsGraph A C N)
        compatible trans hm
      subst n
      refine ⟨⟨⟨w, rfl⟩, hr⟩, ⟨j, p⟩, fun i => ?_⟩
      have hpi := hp i
      rw [allColorings_walk] at hpi
      exact hcolor _ _ hpi⟩
    exact Nat.card_le_card_of_injective emb (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : E => z.val) h))
  have hcount := ColorCounting.colored_roots_bound f hf PC H (fun p i => hP (StatePaths.Path.vertex trans p i))
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hcount
  have hW : Nat.card W ≤ Nat.card (A × Bool) ^ n := by
    have hh := Fintype.card_le_of_injective (fun w : W => w.val) Subtype.val_injective
    rw [Words.card] at hh
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hS := StatePaths.card_path_le trans Q hQ n
  simp only [← Nat.card_eq_fintype_card] at hS
  calc
    _ ≤ Nat.card E * Nat.card C ^ (n+1) := Nat.mul_le_mul_right _ hBE
    _ ≤ Nat.card W * Nat.card (StatePaths.Path trans n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := hcount
    _ ≤ _ := by gcongr

end DiscreteFree.GraphProducer
end

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C : Type*) [Fintype A] [DecidableEq A] [Fintype C]

def Vertex := Σ N : ℕ, (Cayley A N → C) × Cayley A N

instance : Countable (Vertex A C) := inferInstanceAs
  (Countable (Σ N : ℕ, (Cayley A N → C) × Cayley A N))

instance [Nonempty C] : Nonempty (Vertex A C) := ⟨⟨0, (fun _ => Classical.arbitrary C), 1⟩⟩

def sequenceGraph : PortGraph (Vertex A C) (A × Bool) where
  reverse := invertPort A
  reverse_involutive := (cayleyGraph A 0).reverse_involutive
  move z e := ⟨z.1, (allColoringsGraph A C z.1).move z.2 e⟩
  move_reverse z e := by
    rcases z with ⟨N,z⟩
    exact congrArg (Sigma.mk N) ((allColoringsGraph A C N).move_reverse z e)

def sequenceColor (z : Vertex A C) : C := z.2.1 z.2.2

def intoSequence (N : ℕ) (z : (Cayley A N → C) × Cayley A N) : Vertex A C := ⟨N,z⟩

omit [Fintype C] in
@[simp] theorem sequence_move (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (e : A × Bool) :
    (sequenceGraph A C).move (intoSequence A C N z) e =
      intoSequence A C N ((allColoringsGraph A C N).move z e) := rfl

omit [Fintype C] in
@[simp] theorem sequence_walk (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (w : List (A × Bool)) :
    (sequenceGraph A C).walk (intoSequence A C N z) w =
      intoSequence A C N ((allColoringsGraph A C N).walk z w) := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih _

variable {S : Type*}

omit [Fintype C] in

theorem sequence_matched (compatible : Vertex A C → S → Prop) (trans : S → S → Prop)
    (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (j : S) (w : List (A × Bool)) :
    (sequenceGraph A C).Matched compatible trans (intoSequence A C N z) j w ↔
      (allColoringsGraph A C N).Matched (fun z => compatible (intoSequence A C N z)) trans z j w := by
  induction w generalizing z j with
  | nil => rfl
  | cons e w ih =>
    simp only [PortGraph.Matched, sequence_move, ih]

omit [Fintype C] in
theorem sequence_good (compatible : Vertex A C → S → Prop) (trans : S → S → Prop)
    (n N : ℕ) (z : (Cayley A N → C) × Cayley A N) :
    (sequenceGraph A C).Good compatible trans n (intoSequence A C N z) ↔
      (allColoringsGraph A C N).Good (fun z => compatible (intoSequence A C N z)) trans n z := by
  simp only [PortGraph.Good, sequence_matched]
  rfl

end DiscreteFree.GraphProducer
end

end

end OAI
