import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticIdealBertini
import OAI.AlgebraicGeometry.Seshadri.Projective.CoprimeEmbedding
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntegralSectionDimension
import OAI.AlgebraicGeometry.Seshadri.Projective.BertiniSection

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.coprime_integral_section (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ v : Option (Fin N) → ℂ,
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        sectionCombination k s v ≠ 0 ∧ IsIntegral (sectionIdeal k s hs v).subscheme ∧
          topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1 := by
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  obtain ⟨b,hb,hcop,N,s,hs,hc⟩ := S.coprime_embedding_option L hL a ha
  let := hc
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let h := sectionsMorphism k s hs
  have hbase : h ≫ projectiveToSpec = S.structureMap := by
    change _ ≫ projectiveBase = _
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap S.structureMap)
  obtain ⟨v,-,hi,-,heq⟩ :=
    MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section
      S.scheme S.structureMap (L.pow b).sheaf k s hs h rfl hbase 1 one_ne_zero
  have he : sectionIdeal k s hs v = projectiveHyperplane h v := by
    apply sectionIdeal_eq_of_local_equations k s hs v
    intro x
    obtain ⟨U,hx,f,-,hI,e,he⟩ := heq x
    exact ⟨U,hx,f,hI,e,he⟩
  have hne : sectionCombination k s v ≠ 0 := by
    obtain ⟨x⟩ : Nonempty S.scheme := inferInstance
    obtain ⟨U,hx,f,hf,-,e,hef⟩ := heq x
    let : Nonempty U.1 := ⟨⟨x,hx⟩⟩
    intro hz
    have hf' : f ≠ 0 := isRegular_iff_ne_zero.mp hf
    apply hf'
    rw [hz,restrictSection_zero,coefficient_zero,map_zero] at hef
    exact hef.symm
  let : IsIntegral (sectionIdeal k s hs v).subscheme := he.symm ▸ hi
  exact ⟨b,hb,hcop,N,s,hs,v,hne,inferInstance,
    sectionIdeal_dimension_eq_one S.structureMap h hbase (L.pow b) k s hs v hne⟩

end
end MaximalSeshadri.Geometry

end


end OAI
