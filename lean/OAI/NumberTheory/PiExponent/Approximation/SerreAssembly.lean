import OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration
import OAI.NumberTheory.PiExponent.Approximation.TwistPresentations
import OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing

namespace OAI

namespace PiExponent.GeometrySupport.SerreAssembly

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
open TwistPresentations

private abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X : Scheme.{0}} [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (hgenerate : ∀ M : {M : X.Modules // M.IsFinitePresentation},
      ∃ n0, ∃ s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections, s.IsFiniteType)
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  have hbound : ∀ i n q, l ≤ q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (coherentTwistFamily L i n) q,
        x = 0 := by
    intro i n q hq x
    let : i.val.IsFinitePresentation := i.property
    have := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n i.val
    let : ((moduleTwistFunctor L n).obj i.val).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        ((moduleTwistFunctor L n).obj i.val)).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover
      ((moduleTwistFunctor L n).obj i.val) q hq x
  choose n0 s hs using hgenerate
  let presentation (i : {M : X.Modules // M.IsFinitePresentation}) :
      SerreDimensionShift.AcyclicPresentation.{1} (schemeUnit X)
        (coherentTwistFamily L) i := by
    let : (s i).IsFiniteType := hs i
    exact acyclicPresentationOfGenerators.{1} L i (n0 i) (s i) hpow
  exact SerreDimensionShift.eventual_all_positive_ext_zero_of_presentations
    (schemeUnit X) (coherentTwistFamily L) l hbound presentation
      ⟨M, inferInstance⟩

theorem eventual_twist_ext_zero_of_section_cover
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  apply eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    L l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover
    _ hpow M
  intro A
  let : A.val.IsFinitePresentation := A.property
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A.val s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  exact ⟨N, G, hG⟩

end
end PiExponent.GeometrySupport.SerreAssembly

end OAI
