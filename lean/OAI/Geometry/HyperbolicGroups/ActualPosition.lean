import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualOccurrenceShape
import OAI.Geometry.HyperbolicGroups.WalkRawPosition

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def squareField (τ : TwoPath) (i : Fin 4) : rowSupport (.inr (.inr τ)) :=
  ⟨![Sum.inl τ.val.1,Sum.inl τ.val.2,Sum.inr (τ,0),Sum.inr (τ,1)] i,by
    fin_cases i <;> simp [rowSupport,squareSupport]⟩

lemma squareField_injective (τ : TwoPath) : Function.Injective (squareField τ) := by
  intro i j h
  have hh := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> simp [squareField,twoPath_ne τ,Ne.symm (twoPath_ne τ)] at hh ⊢

lemma squareField_surjective (τ : TwoPath) : Function.Surjective (squareField τ) := by
  rintro ⟨v,hv⟩
  have hh : v = Sum.inl τ.val.1 ∨ v = Sum.inl τ.val.2 ∨
      v = Sum.inr (τ,0) ∨ v = Sum.inr (τ,1) := by simpa [rowSupport,squareSupport] using hv
  rcases hh with hh | hh | hh | hh
  · exact ⟨0,Subtype.ext hh.symm⟩
  · exact ⟨1,Subtype.ext hh.symm⟩
  · exact ⟨2,Subtype.ext hh.symm⟩
  · exact ⟨3,Subtype.ext hh.symm⟩

/-- Reindexing uses the original edge/decoration field, never its label value. -/
def rawToPosition : RawPosition n w d → (occurrenceShape n w).Pos (Fintype.card (Six n d))
  | .inl a => .inl (enumTop n w a)
  | .inr (.inl ⟨b,e⟩) => .inr (.inl ⟨enumFan n w b,⟨.inl e.val,by
      simpa only [occurrenceShape,Equiv.symm_apply_apply,rowSupport,Finset.mem_map,
        Function.Embedding.inl_apply,Sum.inl.injEq,exists_eq_right] using e.property⟩⟩)
  | .inr (.inr (.inl (s,i))) => .inr (.inr (.inl ⟨enumSquare n w s,⟨(squareField s.1 i).val,by
      simpa only [occurrenceShape,Equiv.symm_apply_apply,rowSupport] using (squareField s.1 i).property⟩⟩))
  | .inr (.inr (.inr (s,i))) => .inr (.inr (.inr (enumSix n d s,i)))

lemma rawToPosition_injective : Function.Injective (rawToPosition n w d) := by
  intro x y h
  rcases x with a | (⟨b,e⟩ | (⟨q,i⟩ | ⟨v,i⟩)) <;>
    rcases y with a' | (⟨b',e'⟩ | (⟨q',i'⟩ | ⟨v',i'⟩)) <;>
    simp only [rawToPosition,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (enumTop n w).injective h
  · have hb : b = b' := (enumFan n w).injective (congrArg Sigma.fst h)
    subst b'
    have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have he : e = e' := Subtype.ext (Sum.inl.inj (congrArg Subtype.val hf))
    subst e'
    rfl
  · have hq : q = q' := (enumSquare n w).injective (congrArg Sigma.fst h)
    subst q'
    have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hv := congrArg Subtype.val hf
    have hi : i = i' := squareField_injective q.1 (Subtype.ext hv)
    exact Prod.ext rfl hi
  · obtain ⟨hv,hi⟩ := Prod.mk.inj h
    exact Prod.ext ((enumSix n d).injective hv) hi

lemma rawToPosition_surjective : Function.Surjective (rawToPosition n w d) := by
  intro p
  rcases p with a | (⟨b,⟨f,hf⟩⟩ | (⟨q,f⟩ | ⟨v,i⟩))
  · exact ⟨.inl ((enumTop n w).symm a),by simp only [rawToPosition,Equiv.apply_symm_apply]⟩
  · rcases f with e | r
    · have he : e ∈ fan (((enumFan n w).symm b).val.1) := by
        simpa only [occurrenceShape,rowSupport,Finset.mem_map,Function.Embedding.inl_apply,
          Sum.inl.injEq,exists_eq_right] using hf
      refine ⟨.inr (.inl ⟨(enumFan n w).symm b,⟨e,he⟩⟩),?_⟩
      simp only [rawToPosition,Sum.inr.injEq,Sum.inl.injEq]
      refine Sigma.ext ((enumFan n w).apply_symm_apply b) ?_
      exact (Subtype.heq_iff_coe_eq (by intro v; simp only [Equiv.apply_symm_apply])).mpr rfl
    · simp [rowSupport] at hf
  · have hf : f.val ∈ rowSupport (.inr (.inr (((enumSquare n w).symm q).1))) := f.property
    obtain ⟨i,hi⟩ := squareField_surjective (((enumSquare n w).symm q).1) ⟨f.val,hf⟩
    refine ⟨.inr (.inr (.inl ((enumSquare n w).symm q,i))),?_⟩
    simp only [rawToPosition,Sum.inr.injEq,Sum.inl.injEq]
    refine Sigma.ext ((enumSquare n w).apply_symm_apply q) ?_
    exact (Subtype.heq_iff_coe_eq (by intro v; simp only [Equiv.apply_symm_apply])).mpr
      (congrArg Subtype.val hi)
  · exact ⟨.inr (.inr (.inr ((enumSix n d).symm v,i))),by simp only [rawToPosition,Equiv.apply_symm_apply]⟩

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
