import Mathlib

namespace OAI

noncomputable section
namespace PiExponent.CurveMorphismFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

attribute [local instance] specializationOrder

theorem isClosed_singleton_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim' : Order.krullDim X ≤ 1 := by
    change Order.krullDim (IrreducibleCloseds X) ≤ 1 at hdim
    rwa [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at hdim
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim'
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

theorem finite_closed_avoiding_genericPoint (X : Scheme.{u}) [IsIntegral X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hS, hclosed, hirr, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hcover]
  apply hS.sUnion
  intro C hC
  obtain ⟨x, hx⟩ := QuasiSober.sober (hirr C hC) (hclosed C hC)
  have hxne : x ≠ genericPoint X := by
    intro heq
    apply hη
    rw [hcover, ← heq]
    exact mem_sUnion.mpr ⟨C, hC, hx.mem⟩
  have hxc := isClosed_singleton_of_ne_genericPoint X hdim x hxne
  have heq : C = {x} := hx.def.symm.trans hxc.closure_eq
  rw [heq]
  exact finite_singleton x

theorem finite_fibers {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) (y : Y) : (f ⁻¹' {y}).Finite := by
  by_cases hy : IsClosed ({y} : Set Y)
  · have hZ : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
    apply finite_closed_avoiding_genericPoint X hdim hZ
    intro hη
    have hall : (Set.univ : Set X) ⊆ f ⁻¹' {y} :=
      ((genericPoint_spec X).mem_closed_set_iff hZ).mp hη
    obtain ⟨z, hz⟩ := exists_ne y
    obtain ⟨x, hx⟩ := f.surjective z
    apply hz
    have hh := hall (show x ∈ (Set.univ : Set X) from trivial)
    change f x = y at hh
    exact hx.symm.trans hh
  · apply (finite_singleton (genericPoint X)).subset
    intro x hx
    change f x = y at hx
    by_cases hxe : x = genericPoint X
    · exact hxe
    · exfalso
      apply hy
      have hclosed := f.isClosedMap {x} (isClosed_singleton_of_ne_genericPoint X hdim x hxe)
      simpa only [Set.image_singleton, hx] using hclosed

theorem isFinite_of_proper_dominant {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) : IsFinite f := by
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (finite_fibers f hdim)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.CurveMorphismFinite

end

end OAI
