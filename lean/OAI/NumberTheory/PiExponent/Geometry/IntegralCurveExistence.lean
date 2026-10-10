import Mathlib
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

def irreducibleClosedRestrict {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) (W : Set.Iic Z) : IrreducibleCloseds (Z : Set X) where
  carrier := {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)}
  isIrreducible' := by
    have : IrreducibleSpace (W.val : Set X) := Subtype.irreducibleSpace W.val.isIrreducible
    have hi := (IrreducibleSpace.isIrreducible_univ (W.val : Set X)).image
      (Set.inclusion W.property) (continuous_inclusion W.property).continuousOn
    convert hi using 1
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  isClosed' := W.val.isClosed.preimage continuous_subtype_val

def irreducibleClosedsBelowEquiv {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    IrreducibleCloseds (Z : Set X) ≃o Set.Iic Z where
  toFun W := ⟨{
    carrier := Subtype.val '' (W : Set (Z : Set X))
    isIrreducible' := W.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
    isClosed' := Z.isClosed.isClosedMap_subtype_val _ W.isClosed }, by
      rintro _ ⟨x, _, rfl⟩
      exact x.property⟩
  invFun := irreducibleClosedRestrict Z
  left_inv W := by
    ext x
    change x.val ∈ Subtype.val '' (W : Set ↥(Z : Set X)) ↔ x ∈ (W : Set ↥(Z : Set X))
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := Subtype.ext hxy
      exact heq ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv W := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change (Subtype.val : ↥(Z : Set X) → X) '' {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)} = (W.val : Set X)
    apply Set.image_preimage_eq_of_subset
    simpa only [Subtype.range_coe] using (show (W.val : Set X) ⊆ Z from W.property)
  map_rel_iff' := by
    intro W V
    change Subtype.val '' (W : Set (Z : Set X)) ⊆ Subtype.val '' (V : Set (Z : Set X)) ↔ W ≤ V
    exact Set.image_subset_image_iff Subtype.val_injective

theorem topologicalKrullDim_irreducibleClosed {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleClosedsBelowEquiv Z),
    ← Order.height_eq_krullDim_Iic]

theorem exists_irreducibleClosed_dimension_one (X : Type*) [TopologicalSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    ∃ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 := by
  have hdim' : Order.krullDim (IrreducibleCloseds X) = d := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  have hidx : 1 < p.length + 1 := by omega
  refine ⟨p ⟨1, hidx⟩, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed]
  have hh := Order.height_eq_index_of_length_eq_height_last hlast ⟨1, hidx⟩
  simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hh

theorem isReduced_vanishingIdeal_subscheme {X : Scheme} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).mpr
  intro U
  change X.affineOpens at U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  have hI : (I.ideal U).IsRadical := by
    simpa only [I, Scheme.IdealSheafData.vanishingIdeal_ideal] using
      PrimeSpectrum.isRadical_vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  have : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hI
  infer_instance

def integralCurveOfIrreducibleClosed {X : Scheme.{0}} (Z : IrreducibleCloseds X)
    (hZ : topologicalKrullDim (Z : Set X) = 1) : IntegralCurve X := by
  let C : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hs : (I.support : Set X) = (Z : Set X) := by
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme C
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact Subtype.irreducibleSpace Z.isIrreducible
  refine {
    scheme := I.subscheme
    embedding := I.subschemeι
    closedImmersion := inferInstance
    integral := isIntegral_of_irreducibleSpace_of_isReduced _
    dimension := ?_ }
  change topologicalKrullDim (I.support : Set X) = 1
  rw [hs]
  exact hZ

theorem nonempty_integralCurve_of_dimension_pos (X : Scheme.{0})
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    Nonempty (IntegralCurve X) := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_dimension_one X d hdim hd
  exact ⟨integralCurveOfIrreducibleClosed Z hZ⟩

end
end PiExponent.NumericalAmpleness

end OAI
