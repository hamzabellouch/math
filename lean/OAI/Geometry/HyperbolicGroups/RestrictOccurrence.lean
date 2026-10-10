import Mathlib
import OAI.Geometry.HyperbolicGroups.RankCollection
import OAI.Geometry.HyperbolicGroups.WeightedCoincidence

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

variable {s u q v : ℕ} (T : Shape s u q)

/-- Integer weights on the occurrences, with fan slots retained at every level. -/
structure Weights where
  top : Fin s → ℕ
  fan : Fin u → ℕ
  square : Fin q → ℕ
  six : Fin v → ℕ
  slot : ∀ a i, top a ≤ fan (T.2.1 a i).val

namespace Weights
variable {T}
variable (W : T.Weights (v := v))
local instance : DecidableEq (T.Pos v) := Classical.typeDecidableEq _

def position : T.Pos v → ℕ
  | .inl a => W.top a
  | .inr (.inl ⟨b,_⟩) => W.fan b
  | .inr (.inr (.inl ⟨e,_⟩)) => W.square e
  | .inr (.inr (.inr (e,_))) => W.six e

abbrev TopAt (j : ℕ) := {a : Fin s // j < W.top a}
abbrev FanAt (j : ℕ) := {b : Fin u // j < W.fan b}
abbrev SquareAt (j : ℕ) := {e : Fin q // j < W.square e}
abbrev SixAt (j : ℕ) := {e : Fin v // j < W.six e}

abbrev topEnum (j : ℕ) := Fintype.equivFin (W.TopAt j)
abbrev fanEnum (j : ℕ) := Fintype.equivFin (W.FanAt j)
abbrev squareEnum (j : ℕ) := Fintype.equivFin (W.SquareAt j)
abbrev sixEnum (j : ℕ) := Fintype.equivFin (W.SixAt j)

abbrev topIndex (j : ℕ) (a : Fin (Fintype.card (W.TopAt j))) : Fin s := ((W.topEnum j).symm a).val
abbrev fanIndex (j : ℕ) (b : Fin (Fintype.card (W.FanAt j))) : Fin u := ((W.fanEnum j).symm b).val
abbrev squareIndex (j : ℕ) (e : Fin (Fintype.card (W.SquareAt j))) : Fin q := ((W.squareEnum j).symm e).val
abbrev sixIndex (j : ℕ) (e : Fin (Fintype.card (W.SixAt j))) : Fin v := ((W.sixEnum j).symm e).val

/-- The literal collection at level j; a retained top keeps every fan slot. -/
def atLevel (j : ℕ) : Shape (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) :=
  ⟨fun b => T.1 (W.fanIndex j b),
    (fun a i => ⟨W.fanEnum j ⟨(T.2.1 (W.topIndex j a) i).val,
      lt_of_lt_of_le ((W.topEnum j).symm a).property (W.slot _ i)⟩, by
        simp only [fanIndex,Equiv.symm_apply_apply]
        exact (T.2.1 (W.topIndex j a) i).property⟩),
    fun e => T.2.2 (W.squareIndex j e)⟩

/-- Positions and trials embed in the unchanged original arrays. -/
def embedPosition (j : ℕ) : (W.atLevel j).Pos (Fintype.card (W.SixAt j)) → T.Pos v
  | .inl a => .inl (W.topIndex j a)
  | .inr (.inl ⟨b,f⟩) => .inr (.inl ⟨W.fanIndex j b,f⟩)
  | .inr (.inr (.inl ⟨e,f⟩)) => .inr (.inr (.inl ⟨W.squareIndex j e,f⟩))
  | .inr (.inr (.inr (e,i))) => .inr (.inr (.inr (W.sixIndex j e,i)))

def embedTrial (j : ℕ) : Trial (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) (Fintype.card (W.SixAt j)) → Trial s u q v
  | .inl a => .inl (W.topIndex j a)
  | .inr (.inl b) => .inr (.inl (W.fanIndex j b))
  | .inr (.inr (.inl e)) => .inr (.inr (.inl (W.squareIndex j e)))
  | .inr (.inr (.inr e)) => .inr (.inr (.inr (W.sixIndex j e)))

lemma embedPosition_injective (j : ℕ) : Function.Injective (W.embedPosition j) := by
  intro x y h
  rcases x with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩)) <;>
    rcases y with a' | (⟨b',f'⟩ | (⟨e',f'⟩ | ⟨e',i'⟩)) <;>
    simp only [embedPosition,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (W.topEnum j).symm.injective (Subtype.ext h)
  · have hb : b = b' := (W.fanEnum j).symm.injective (Subtype.ext (congrArg Sigma.fst h))
    subst b'
    cases h
    rfl
  · have he : e = e' := (W.squareEnum j).symm.injective (Subtype.ext (congrArg Sigma.fst h))
    subst e'
    cases h
    rfl
  · obtain ⟨he,hi⟩ := Prod.mk.inj h
    exact Prod.ext ((W.sixEnum j).symm.injective (Subtype.ext he)) hi

lemma embedTrial_injective (j : ℕ) : Function.Injective (W.embedTrial j) := by
  intro x y h
  rcases x with a | (b | (e | e)) <;>
    rcases y with a' | (b' | (e' | e')) <;>
    simp only [embedTrial,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (W.topEnum j).symm.injective (Subtype.ext h)
  · exact (W.fanEnum j).symm.injective (Subtype.ext h)
  · exact (W.squareEnum j).symm.injective (Subtype.ext h)
  · exact (W.sixEnum j).symm.injective (Subtype.ext h)

lemma image_embedPosition (j : ℕ) : Finset.univ.image (W.embedPosition j) =
    Finset.univ.filter (fun p => j < W.position p) := by
  ext p
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨x,rfl⟩
    rcases x with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
    · exact ((W.topEnum j).symm a).property
    · exact ((W.fanEnum j).symm b).property
    · exact ((W.squareEnum j).symm e).property
    · exact ((W.sixEnum j).symm e).property
  · intro hp
    rcases p with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
    · exact ⟨.inl (W.topEnum j ⟨a,hp⟩),by simp only [embedPosition,topIndex,Equiv.symm_apply_apply]⟩
    · refine ⟨.inr (.inl ⟨W.fanEnum j ⟨b,hp⟩,⟨f.val,?_⟩⟩),?_⟩
      · simpa only [atLevel,fanIndex,Equiv.symm_apply_apply] using f.property
      · simp only [embedPosition,Sum.inr.injEq,Sum.inl.injEq]
        refine Sigma.ext ?_ ?_
        · exact congrArg Subtype.val ((W.fanEnum j).symm_apply_apply ⟨b,hp⟩)
        · refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
          · intro x; simp only [fanIndex,Equiv.symm_apply_apply]
          · rfl
    · refine ⟨.inr (.inr (.inl ⟨W.squareEnum j ⟨e,hp⟩,⟨f.val,?_⟩⟩)),?_⟩
      · simpa only [atLevel,squareIndex,Equiv.symm_apply_apply] using f.property
      · simp only [embedPosition,Sum.inr.injEq,Sum.inl.injEq]
        refine Sigma.ext ?_ ?_
        · exact congrArg Subtype.val ((W.squareEnum j).symm_apply_apply ⟨e,hp⟩)
        · refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
          · intro x; simp only [squareIndex,Equiv.symm_apply_apply]
          · rfl
    · exact ⟨.inr (.inr (.inr (W.sixEnum j ⟨e,hp⟩,i))),by simp only [embedPosition,sixIndex,Equiv.symm_apply_apply]⟩

lemma coreCoord_embed (j : ℕ) (a : Fin (Fintype.card (W.TopAt j))) (e : Edge) :
    W.embedPosition j ((W.atLevel j).coreCoord (v := Fintype.card (W.SixAt j)) a e) =
      T.coreCoord (v := v) (W.topIndex j a) e := by
  simp only [coreCoord]
  split_ifs <;> simp [embedPosition,atLevel,fanIndex]
  refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
  · intro f; simp only [Equiv.symm_apply_apply]
  · rfl

lemma row_embed {A : Type*} (j : ℕ) (σ : T.Pos v → A)
    (r : Trial (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) (Fintype.card (W.SixAt j))) :
    (W.atLevel j).row (σ ∘ W.embedPosition j) r = T.row σ (W.embedTrial j r) := by
  rcases r with a | (b | (e | e))
  · simp only [row,embedTrial]
    apply congrArg Sum.inl
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    funext f
    rcases f with ⟨f,hf⟩
    rcases f with e | x
    · simp only [Function.comp_apply,topCoord,coreCoord_embed]
    · simp [rowSupport] at hf
  · rfl
  · rfl
  · rfl

lemma rank_embed {n : ℕ} (j : ℕ) (σ : T.Pos v → SymmetricAlphabet n) :
    Coincidence.unsignedRank (σ ∘ W.embedPosition j) =
      Coincidence.rankOn (fun p => (σ p).1) (Finset.univ.filter (fun p => j < W.position p)) := by
  rw [← image_embedPosition]
  simp only [Coincidence.unsignedRank,Coincidence.rankOn,Coincidence.unsignedValues,
    Finset.card_image_of_injective _ (W.embedPosition_injective j),Finset.card_univ,
    Finset.image_image,Function.comp_def]

/-- Any good bounded-rank table supplies the full weighted-level estimates on
actual field positions; the restricted collection is reindexed rather than
assumed to satisfy a new condition. -/
theorem rank_level_bound {M n : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ) (j : ℕ) :
    (Coincidence.rankOn (fun p => (σ p).1) (Finset.univ.filter (fun p => j < W.position p)) : ℝ) ≤
      ((3-β)-7*(2-α)) * Fintype.card (W.TopAt j) + (2-α) * Fintype.card (W.FanAt j) +
        (2-δ) * Fintype.card (W.SquareAt j) + (3-δ) * Fintype.card (W.SixAt j) := by
  have hh := h.rank_bound (v := Fintype.card (W.SixAt j)) (W.atLevel j)
    ((Fintype.card_subtype_le _).trans (by simpa using hs))
    ((Fintype.card_subtype_le _).trans (by simpa using hu))
    ((Fintype.card_subtype_le _).trans (by simpa using hq))
    ((Fintype.card_subtype_le _).trans (by simpa using hv))
  rw [← W.rank_embed j σ]
  apply hh
  · intro a b hab
    simp only [W.row_embed] at hab
    exact W.embedTrial_injective j (hi hab)
  · intro r
    rw [W.row_embed]
    exact hp _

end Weights
end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end

end OAI
