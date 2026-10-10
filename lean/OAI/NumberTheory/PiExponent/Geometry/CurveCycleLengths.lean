import OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal

def stalkLength (Y : Scheme.{0}) (y : Y) : ℕ∞ :=
  Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y)

theorem zero_stalk_lengthNat_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (zeroIdeal L s).subscheme) :
    letI : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      Fintype.ofFinite _
    (stalkLength (zeroIdeal L s).subscheme y).toNat =
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        componentMultiplicity X C.val *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
            (pullbackSection (reducedComponentι X C.val) s)).subscheme
              ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat := by
  classical
  let : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
    Fintype.ofFinite _
  let f := fun C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} =>
    (componentMultiplicity X C.val : ℕ∞) *
      stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
        (pullbackSection (reducedComponentι X C.val) s)).subscheme
          ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)
  have hlocal : stalkLength (zeroIdeal L s).subscheme y = ∑ C, f C := by
    obtain ⟨U,hy,⟨e⟩,_⟩ := common_affine_frames L L ((zeroIdeal L s).subschemeι y)
    refine (zero_stalk_length_eq_component_sum hd L s U e y hy).trans ?_
    apply Finset.sum_congr rfl
    intro C _
    exact congrArg (fun n : ℕ∞ => (componentMultiplicity X C.val : ℕ∞) * n)
      (componentLocalCutLength_eq_zero_stalk_at L s C.val ⟨y,C.property⟩ U e hy)
  have hsum : ∑ C, f C ≠ ⊤ := by
    rw [← hlocal]
    exact zero_stalk_length_ne_top hd L s y
  have hn := congrArg ENat.toNat hlocal
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsum)] at hn
  simpa only [f,ENat.toNat_mul,ENat.toNat_natCast] using hn

theorem zero_lengthNat_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    [Fintype (irreducibleComponents X)] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    [Fintype (zeroIdeal L s).subscheme] :
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
      ∑ C : irreducibleComponents X, componentMultiplicity X C *
        ∑ z, (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat := by
  classical
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  calc
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
        ∑ y : (zeroIdeal L s).subscheme,
          ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
            componentMultiplicity X C.val *
              (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
                (pullbackSection (reducedComponentι X C.val) s)).subscheme
                  ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat :=
      Finset.sum_congr rfl (fun y _ => zero_stalk_lengthNat_eq_component_sum hd L s y)
    _ = ∑ C : irreducibleComponents X, ∑ z,
        componentMultiplicity X C *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat :=
      sum_component_zero_incidence L s (fun C z => componentMultiplicity X C *
        (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat)
    _ = _ := Finset.sum_congr rfl (fun C _ => (Finset.mul_sum _ _ _).symm)

end
end PiExponent.CurveCycle

end OAI
