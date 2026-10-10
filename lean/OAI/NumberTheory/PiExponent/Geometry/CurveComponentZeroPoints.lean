import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport
import OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

def componentZeroToGlobal {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subscheme := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  refine ⟨i (J.subschemeι z), ?_⟩
  have hz := z.property
  change J.subschemeι z ∈ (J.support : Set (reducedComponent X C)) at hz
  change i (J.subschemeι z) ∈ ((zeroIdeal L s).support : Set X)
  erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)] at hz
  erw [zeroIdeal_support L s]
  change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
  rw [pullback_isoOpen_eq L s i] at hz
  exact hz

theorem componentZeroToGlobal_mem {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ C.val :=
  reducedComponentι_mem X C _

def componentZeroPointEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X) :
    (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme ≃
    {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val} := by
  let i := reducedComponentι X C
  let I := zeroIdeal L s
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let g : J.subscheme → {y : I.subscheme // I.subschemeι y ∈ C.val} :=
    fun z => ⟨componentZeroToGlobal L s C z,componentZeroToGlobal_mem L s C z⟩
  apply Equiv.ofBijective g
  constructor
  · intro z w h
    apply J.subschemeι.isEmbedding.injective
    apply i.isEmbedding.injective
    exact congrArg (fun q => I.subschemeι q.val) h
  · intro y
    have hymem : I.subschemeι y.val ∈ Set.range i := by
      rw [reducedComponentι_range]
      exact y.property
    obtain ⟨z,hz⟩ := hymem
    have hzJ : z ∈ (J.support : Set (reducedComponent X C)) := by
      erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)]
      change z ∉ isoOpen (pullbackSection i s)
      rw [pullback_isoOpen_eq L s i]
      change i z ∉ isoOpen s
      rw [hz]
      have hy := y.val.property
      change I.subschemeι y.val ∈ (I.support : Set X) at hy
      erw [zeroIdeal_support L s] at hy
      exact hy
    refine ⟨⟨z,hzJ⟩, ?_⟩
    apply Subtype.ext
    apply I.subschemeι.isEmbedding.injective
    exact hz

instance finite_componentZero {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    [Finite (zeroIdeal L s).subscheme] :
    Finite (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
  Finite.of_equiv _ (componentZeroPointEquiv L s C).symm

end
end PiExponent.CurveCycle

end OAI
