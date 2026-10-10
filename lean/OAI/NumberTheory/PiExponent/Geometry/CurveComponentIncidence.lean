import OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

def sectionZeroIncidenceEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) :
    (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) ≃
    (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) where
  toFun p := ⟨p.2.val, (componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩⟩
  invFun q := ⟨(componentZeroPointEquiv L s q.1 q.2).val,
    ⟨q.1,(componentZeroPointEquiv L s q.1 q.2).property⟩⟩
  left_inv p := by
    rcases p with ⟨y,C,hC⟩
    dsimp only
    have h := (componentZeroPointEquiv L s C).apply_symm_apply ⟨y,hC⟩
    exact congrArg (fun t : {y : (zeroIdeal L s).subscheme //
      (zeroIdeal L s).subschemeι y ∈ C.val} =>
      (⟨t.val,⟨C,t.property⟩⟩ : Σ y : (zeroIdeal L s).subscheme,
        {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val})) h
  right_inv q := by
    rcases q with ⟨C,z⟩
    dsimp only
    exact congrArg (Sigma.mk C) ((componentZeroPointEquiv L s C).symm_apply_apply z)

theorem sum_component_zero_incidence {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Fintype (irreducibleComponents X)]
    [Fintype (zeroIdeal L s).subscheme]
    {R : Type*} [AddCommMonoid R]
    (w : ∀ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme → R) :
    letI : ∀ y : (zeroIdeal L s).subscheme,
      Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
        fun _ => Fintype.ofFinite _
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme,
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        w C.val ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)) =
      ∑ C : irreducibleComponents X, ∑ z, w C z := by
  classical
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
  let a : (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) → R :=
    fun p => w p.2.val ((componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩)
  let b : (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) → R :=
    fun q => w q.1 q.2
  exact (Fintype.sum_sigma a).symm.trans
    ((Fintype.sum_equiv (sectionZeroIncidenceEquiv L s) a b (fun _ => rfl)).trans
      (Fintype.sum_sigma b))

end
end PiExponent.CurveCycle

end OAI
