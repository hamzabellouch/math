import OAI.Combinatorics.Ramsey.CycleClique.Construction.ProfileMasks
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawEmbedding
import Mathlib.Data.List.OfFn

namespace OAI

/-! A finite layout is verified by its chain lengths, clique-position masks
and exhaustive indexing. Its realization then uses the actual chain vertices. -/

namespace CycleClique.Construction
variable {V W : Type*}

theorem chainCollection_eq_of_flatten_lengths {C D : List (List V)}
    (hf : C.flatten = D.flatten) (hl : C.map List.length = D.map List.length) : C = D := by
  induction C generalizing D with
  | nil =>
    cases D with
    | nil => rfl
    | cons d D => simp at hl
  | cons c C ih =>
    cases D with
    | nil => simp at hl
    | cons d D =>
      have hlen : c.length = d.length := (List.cons.inj hl).1
      have htail := (List.cons.inj hl).2
      have heq : c ++ C.flatten = d ++ D.flatten := hf
      obtain ⟨rfl, hr⟩ := List.append_inj heq hlen
      exact congrArg (List.cons c) (ih hr htail)

def layoutGraph [DecidableEq W] (Q : Finset W) (D : List (List W)) : SimpleGraph W where
  Adj i j := i ≠ j ∧ ((i ∈ Q ∧ j ∈ Q) ∨
    ∃ l ∈ D, [i, j] <:+: l ∨ [j, i] <:+: l)
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hQ | ⟨l, hl, he⟩
    · exact Or.inl hQ.symm
    · exact Or.inr ⟨l, hl, he.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance [DecidableEq W] (Q : Finset W) (D : List (List W)) :
    DecidableRel (layoutGraph Q D).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

variable {G : SimpleGraph V} {Q : Finset V}

theorem RawPathSystem.realize_layout (S : RawPathSystem G Q) {n : ℕ}
    {P : List (List ℕ)} (hp : List.Forall₂ (AssignedAmounts Q) S.chains P)
    (hne : ∀ l ∈ S.chains, l ≠ []) (hQ : G.IsClique (Q : Set V))
    (D : List (List (Fin n))) (Q₀ : Finset (Fin n))
    (hindex : D.flatten = List.finRange n)
    (hlength : D.map List.length = P.map (fun w => w.sum + w.length + 1))
    (hmask : D.map (cliqueMask Q₀) = P.map profileMask) :
    ∃ f : Fin n → V, Function.Injective f ∧
      D.map (List.map f) = S.chains ∧
      (∀ i, f i ∈ Q ↔ i ∈ Q₀) ∧
      (∀ {i j}, (layoutGraph Q₀ D).Adj i j → G.Adj (f i) (f j)) := by
  classical
  have hactual : S.chains.map List.length = P.map (fun w => w.sum + w.length + 1) := profiles_lengths hp hne
  have hlengths : D.map List.length = S.chains.map List.length := hlength.trans hactual.symm
  have hN : S.chains.flatten.length = n := by
    rw [List.length_flatten, ← hlengths, ← List.length_flatten, hindex, List.length_finRange]
  subst n
  let f : Fin S.chains.flatten.length → V := S.chains.flatten.get
  have hf : Function.Injective f := S.flatten_nodup.injective_get
  have hmap : D.map (List.map f) = S.chains := by
    apply chainCollection_eq_of_flatten_lengths
    · rw [← List.map_flatten, hindex]
      exact List.map_get_finRange _
    · simpa only [List.map_map, Function.comp_def, List.length_map] using hlengths
  have hmasks : S.chains.map (cliqueMask Q) = D.map (cliqueMask Q₀) :=
    (profiles_masks hp hne).trans hmask.symm
  have hmembership : ∀ i, f i ∈ Q ↔ i ∈ Q₀ := by
    have hh := (congrArg (fun C : List (List V) =>
      (C.map (cliqueMask Q)).flatten) hmap).trans (congrArg List.flatten hmasks)
    simp only [cliqueMask, List.map_map, Function.comp_def, ← List.map_flatten, hindex] at hh
    have hright : (D.map (cliqueMask Q₀)).flatten =
        (List.finRange S.chains.flatten.length).map (fun i => decide (i ∈ Q₀)) := by
      have hm : D.map (cliqueMask Q₀) =
          D.map (fun l => l.map (fun i => decide (i ∈ Q₀))) := by
        apply List.map_congr_left
        intro l hl
        exact cliqueMask_eq_map Q₀ l
      rw [hm, ← List.map_flatten, hindex]
    have hh' := hh.trans hright
    intro i
    have he := List.map_inj_left.mp hh' i (List.mem_finRange i)
    exact decide_eq_decide.mp he
  refine ⟨f, hf, hmap, hmembership, ?_⟩
  intro i j hij
  rcases hij.2 with hijQ | ⟨l, hl, hijl⟩
  · exact hQ ((hmembership i).mpr hijQ.1) ((hmembership j).mpr hijQ.2)
      (fun he => hij.1 (hf he))
  · have hpath : (l.map f).IsChain G.Adj := (S.paths _ (by
      exact Eq.mp (congrArg (fun C : List (List V) => l.map f ∈ C) hmap)
        (List.mem_map.mpr ⟨l, hl, rfl⟩))).2
    rcases hijl with hijl | hjil
    · have hh := hpath.infix (hijl.map f)
      exact (List.isChain_cons_cons.mp hh).1
    · have hh := hpath.infix (hjil.map f)
      exact (List.isChain_cons_cons.mp hh).1.symm

end CycleClique.Construction

end OAI
