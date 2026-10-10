import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}}

theorem nonconstant_of_closedImmersion_on_open (f : C ⟶ X)
    (hdim : topologicalKrullDim C = 1) (U : X.Opens)
    [IsClosedImmersion (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    ¬ ∃ x : X, Set.range f ⊆ {x} := by
  rintro ⟨x, hx⟩
  have he : ∀ c : C, f c = x := fun c => hx ⟨c, rfl⟩
  obtain ⟨q⟩ := hU
  have hxU : x ∈ U := (he q.1) ▸ q.2
  let : Subsingleton C := ⟨fun a b => by
    have ha : f a ∈ U := (he a).symm ▸ hxU
    have hb : f b ∈ U := (he b).symm ▸ hxU
    have hab : (f ∣_ U) (⟨a,ha⟩ : (f ⁻¹ᵁ U).toScheme) =
        (f ∣_ U) (⟨b,hb⟩ : (f ⁻¹ᵁ U).toScheme) := by
      apply Subtype.ext
      exact (morphismRestrict_base_coe f U ⟨a, ha⟩).trans
        ((he a).trans ((he b).symm.trans (morphismRestrict_base_coe f U ⟨b, hb⟩).symm))
    exact congrArg Subtype.val ((f ∣_ U).isEmbedding.injective hab)⟩
  have hh := topologicalKrullDim_zero_of_discreteTopology C
  rw [hdim] at hh
  norm_num at hh

theorem exists_image_outside_closed_points [IsIntegral C] (f : C ⟶ X)
    (Z : Set X) (hZ : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hn : ¬ ∃ x : X, Set.range f ⊆ {x}) : ∃ c : C, f c ∉ Z := by
  by_contra h
  push Not at h
  have hc := hZ (f (genericPoint C)) (h (genericPoint C))
  apply hn
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c,rfl⟩
  have hh := ((genericPoint_spec C).specializes (Set.mem_univ c)).map f.continuous
  have hm := hh.mem_closure
  rwa [hc.closure_eq] at hm

end PiExponent.CurveBlowupImage

end

end OAI
