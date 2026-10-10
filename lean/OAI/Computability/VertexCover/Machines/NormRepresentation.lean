import Mathlib
import OAI.Computability.VertexCover.Analysis.Restriction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                       
section

namespace VertexCover.LabelCover
 theorem finset_lift_injective {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (I : Finset β) (hI : ∀ p ∈ I, ∃ a, f a=p) :
    ∃ S : Finset α, S.image f=I ∧ Set.InjOn f S := by
  classical
  let g : I → α := fun p => (hI p p.property).choose
  have hg (p : I) : f (g p)=p := (hI p p.property).choose_spec
  refine ⟨Finset.univ.image g,?_,?_⟩
  · ext p
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,⟨q,rfl⟩,rfl⟩; rw [hg]; exact q.property
    · intro hp; exact ⟨g ⟨p,hp⟩,⟨⟨p,hp⟩,rfl⟩,hg ⟨p,hp⟩⟩
  · intro a ha b hb h
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hb
    rw [hg,hg] at h
    exact congrArg g (Subtype.ext h)
 theorem norm_le_representations (Φ : LabelCover) {d : ℕ} {α : Type*} [Fintype α]
    (f : α → Φ.Coordinate d) (z : Φ.Coordinate d → ℝ) (B : Finset (Φ.Query d))
    (hz : ∀ p, p.1 ∉ B → z p=0)
    (hc : ∀ p : Φ.Coordinate d, p.1 ∈ B → ∃ a, f a=p) (C : ℝ) :
    Φ.compatibilityNorm z ≤ C ↔
      ∀ S : Finset α, Set.InjOn f S → Φ.Compatible (S.image f) → |∑ a ∈ S, z (f a)| ≤ C := by
  classical
  constructor
  · intro h S hi hs
    have he : ∑ p ∈ S.image f, z p = ∑ a ∈ S, z (f a) := Finset.sum_image hi
    rw [← he]
    exact (Φ.form_le_norm z _ hs).trans h
  · intro h
    obtain ⟨I,hi,hb,he⟩ := Φ.norm_attained_on_support z B hz
    obtain ⟨S,hs,hinj⟩ := finset_lift_injective f I (fun p hp => hc p (hb p hp))
    rw [he,← hs,Finset.sum_image hinj]
    exact h S hinj (hs.symm ▸ hi)
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
