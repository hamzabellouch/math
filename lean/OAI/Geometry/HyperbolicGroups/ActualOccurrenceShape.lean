import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget
import OAI.Geometry.HyperbolicGroups.Shape

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

noncomputable instance : Fintype (Top n w) := Fintype.ofFinite _
noncomputable instance : Fintype (Fan n w) := Fintype.ofFinite _
noncomputable instance : Fintype (Square n w) := Fintype.ofFinite _
noncomputable instance : Fintype (Six n d) := Fintype.ofFinite _

abbrev enumTop := Fintype.equivFin (Top n w)
abbrev enumFan := Fintype.equivFin (Fan n w)
abbrev enumSquare := Fintype.equivFin (Square n w)
abbrev enumSix := Fintype.equivFin (Six n d)

/-- One index for every actual included trial, with all seven fan slots and
no duplication of a top by its boundary cycle or by decoration coordinates. -/
def occurrenceShape : Occurrences.Shape (Fintype.card (Top n w))
    (Fintype.card (Fan n w)) (Fintype.card (Square n w)) :=
  ⟨fun b => ((enumFan n w).symm b).val.1,
    (fun a i => ⟨enumFan n w (slot n w ((enumTop n w).symm a) i), by
      simp only [Equiv.symm_apply_apply]; rfl⟩),
    fun e => ((enumSquare n w).symm e).1⟩

/-- The literal signed values at original field positions. -/
def occurrenceValues : (occurrenceShape n w).Pos (Fintype.card (Six n d)) → Alphabet n
  | .inl a => ((enumTop n w).symm a).val loose
  | .inr (.inl ⟨b,f⟩) => ((enumFan n w).symm b).val.2 f
  | .inr (.inr (.inl ⟨e,f⟩)) => ((enumSquare n w).symm e).2.val f
  | .inr (.inr (.inr (e,i))) => ((enumSix n d).symm e).val i

lemma loose_unique (e : IncidenceTemplate.Edge) (he : isLoose e) : e = loose := by
  exact Subtype.ext he

lemma fan_value_congr {b b' : Fan n w} (hb : b = b') (e : IncidenceTemplate.Edge)
    (he : Sum.inl e ∈ rowSupport (.inl b.val.1))
    (he' : Sum.inl e ∈ rowSupport (.inl b'.val.1)) :
    b.val.2 ⟨.inl e,he⟩ = b'.val.2 ⟨.inl e,he'⟩ := by
  cases hb
  rfl

lemma occurrence_core_value (a : Fin (Fintype.card (Top n w))) (e : IncidenceTemplate.Edge) :
    occurrenceValues n w d ((occurrenceShape n w).coreCoord a e) = ((enumTop n w).symm a).val e := by
  unfold Occurrences.Shape.coreCoord
  split_ifs with he
  · change ((enumTop n w).symm a).val loose = _
    rw [loose_unique e he]
  · apply fan_value_congr n w ((enumFan n w).symm_apply_apply
      (slot n w ((enumTop n w).symm a) (pointOfRepresentative e.val.1))) e
    simp [rowSupport, slot, fan]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl, he⟩

abbrev OccurrenceTrial := Occurrences.Shape.Trial (Fintype.card (Top n w))
  (Fintype.card (Fan n w)) (Fintype.card (Square n w)) (Fintype.card (Six n d))

def occurrenceTrial : OccurrenceTrial n w d → Occurrences.Entry (Alphabet n)
  | .inl a => .inl (TableModel.row rowSupport (extendCore n ((enumTop n w).symm a).val) (.inr (.inl ())))
  | .inr (.inl b) => .inl ⟨.inl ((enumFan n w).symm b).val.1, ((enumFan n w).symm b).val.2⟩
  | .inr (.inr (.inl e)) => .inl ⟨.inr (.inr ((enumSquare n w).symm e).1), ((enumSquare n w).symm e).2.val⟩
  | .inr (.inr (.inr e)) => .inr ((enumSix n d).symm e).val

lemma occurrence_row (r : OccurrenceTrial n w d) :
    (occurrenceShape n w).row (occurrenceValues n w d) r = occurrenceTrial n w d r := by
  rcases r with a | (b | (e | e))
  · apply congrArg Sum.inl
    change (⟨.inr (.inl ()),_⟩ : TableModel.Entry rowSupport) = ⟨.inr (.inl ()),_⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    funext f
    rcases f with ⟨f,hf⟩
    rcases f with e | g
    · exact occurrence_core_value n w d a e
    · simp [rowSupport] at hf
  · rfl
  · rfl
  · rfl

lemma occurrenceTrial_injective : Function.Injective (occurrenceTrial n w d) := by
  intro x y h
  rcases x with a | (b | (e | f)) <;> rcases y with a' | (b' | (e' | f'))
  · apply congrArg Sum.inl
    apply (enumTop n w).symm.injective
    apply Subtype.ext
    exact top_row_injective n (Sum.inl.inj h)
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases h
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · apply congrArg (Sum.inr ∘ Sum.inl)
    apply (enumFan n w).symm.injective
    apply Subtype.ext
    have hh := Sum.inl.inj h
    change (⟨.inl _,_⟩ : TableModel.Entry rowSupport) = ⟨.inl _,_⟩ at hh
    have hb := Sum.inl.inj (congrArg Sigma.fst hh)
    apply Sigma.ext hb
    exact (Sigma.mk.inj_iff.mp hh).2
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases h
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · apply congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl)
    apply (enumSquare n w).symm.injective
    have hinj : Function.Injective (fun x : Square n w =>
        (⟨.inr (.inr x.1),x.2.val⟩ : TableModel.Entry rowSupport)) := by
      rintro ⟨e,⟨v,hv⟩⟩ ⟨e',⟨v',hv'⟩⟩ hh
      have he : e = e' := Sum.inr.inj (Sum.inr.inj (congrArg Sigma.fst hh))
      subst e'
      have hvv : v = v' := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
      subst v'
      rfl
    exact hinj (Sum.inl.inj h)
  · cases h
  · cases h
  · cases h
  · cases h
  · apply congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inr)
    apply (enumSix n d).symm.injective
    exact Subtype.ext (Sum.inr.inj h)

lemma occurrence_row_injective : Function.Injective ((occurrenceShape n w).row (occurrenceValues n w d)) := by
  intro x y h
  rw [occurrence_row,occurrence_row] at h
  exact occurrenceTrial_injective n w d h

lemma occurrence_present : BernoulliCandidates.Present (occurrenceShape n w).row
    (Sum.elim w d) (occurrenceValues n w d) := by
  intro r
  rw [occurrence_row]
  rcases r with a | (b | (e | e))
  · exact ((enumTop n w).symm a).property.1
  · exact ((enumFan n w).symm b).property
  · exact ((enumSquare n w).symm e).2.property
  · exact ((enumSix n d).symm e).property

end HyperbolicObstruction.ConeSkeleton
end

end OAI
