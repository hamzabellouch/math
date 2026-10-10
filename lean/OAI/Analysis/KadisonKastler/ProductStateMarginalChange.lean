import OAI.Analysis.KadisonKastler.CyclicStateCompression

namespace OAI

/-! # Changing one marginal of a product state

A faithful GNS representation of one marginal allows any other state on that
algebra to be extended to the GNS operator algebra. Pulling it back through the
cyclic compression changes precisely that marginal of the product state.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder B] [StarOrderedRing B] in
theorem gnsCompression_product
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (φ : C →L[ℂ] ℂ) (hφ : IsState φ)
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ)
    (hprod : ∀ a b, φ (ι a*κ b)=f a*g b)
    (hres : ∀ a, f a=φ (ι a)) (a : A) (b : B) :
    gnsCompression (positiveOfSquares φ hφ.2) (positiveOfSquares f hf.2) ι hres
      (ι a*κ b)=g b • (positiveOfSquares f hf.2).gnsStarAlgHom a := by
  apply gnsCompression_eq_of_pairings
  intro x y
  have he : star (ι x)*(ι a*κ b)*ι y=ι (star x*a*y)*κ b := by
    simp only [map_mul,map_star,mul_assoc]
    rw [(hcomm y b).eq]
  change φ (star (ι x)*(ι a*κ b)*ι y)=_
  rw [he,hprod]
  simp only [smul_apply,inner_smul_right]
  rw [gns_matrix_coefficient]
  exact mul_comm _ _

theorem exists_product_state_change_left
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (φ : C →L[ℂ] ℂ) (hφ : IsState φ)
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g)
    (hprod : ∀ a b, φ (ι a*κ b)=f a*g b)
    (hfaith : Function.Injective (positiveOfSquares f hf.2).gnsStarAlgHom)
    (f' : A →L[ℂ] ℂ) (hf' : IsState f') :
    ∃ ψ : C →L[ℂ] ℂ, IsState ψ ∧ ∀ a b, ψ (ι a*κ b)=f' a*g b := by
  let P := positiveOfSquares φ hφ.2
  let Q := positiveOfSquares f hf.2
  have hres (a : A) : Q a=P (ι a) := by
    change f a=φ (ι a)
    have h := hprod a 1
    simpa only [map_one,mul_one,((isState_iff g).mp hg).1] using h.symm
  obtain ⟨F,hF,hFres⟩ := exists_state_extension_of_embedding Q.gnsStarAlgHom hfaith f' hf'
  let E := gnsCompression P Q ι hres
  refine ⟨F.comp E,gnsCompression_state P Q ι hres F hF,?_⟩
  intro a b
  have he : E (ι a*κ b)=g b • Q.gnsStarAlgHom a :=
    gnsCompression_product ι κ hcomm φ hφ f hf g hprod hres a b
  change F (E (ι a*κ b))=_
  rw [he,map_smul]
  have hval : F (Q.gnsStarAlgHom a)=f' a :=
    congrArg (fun L : A →L[ℂ] ℂ => L a) hFres
  rw [hval]
  exact mul_comm _ _

end

end KadisonKastler

end OAI
