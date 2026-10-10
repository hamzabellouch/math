import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexSecondPageCycles
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexHorizontalBoundary

namespace OAI

/-! # Total homology finiteness from the second page

Both kinds of leading boundary are removed explicitly: horizontal boundaries
by row cycles, then vertical boundaries by the earlier column reduction.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module
variable {R : Type} [CommRing R] (K : NatBicomplex R)

theorem zero_secondPage_class_lowers_filtration (n p j : ℕ) (h : p + j = n)
    (x : boundedTotalCycles K n (p + 1))
    (hx : boundedTotalSecondPageClass K n p j h x = 0) :
    (K.total (ComplexShape.down ℕ)).homologyπ n x.val ∈ filteredTotalHomology K n p := by
  obtain ⟨a, ha⟩ := exists_boundary_of_homologyπ_eq_zero (rowHomologyComplex K j) p
    (boundedTotalSecondPageCycles K n p j h x) hx
  rw [boundedTotalSecondPageCycles_apply] at ha
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective ((K.X (p + 1)).homologyπ j)).mp
    inferInstance a
  let z := horizontalBoundaryCycle K n p j h w
  have hz : boundedTotalLeadingHomology K n p j h z =
      boundedTotalLeadingHomology K n p j h x := by
    rw [horizontalBoundaryCycle_leading_homology, hw]
    exact ha
  have hres : boundedTotalLeadingHomology K n p j h (x - z) = 0 := by
    rw [map_sub, hz, sub_self]
  have hlow := zero_leading_class_lowers_filtration K n p j h (x - z) hres
  have he : (K.total (ComplexShape.down ℕ)).homologyπ n (x - z).val =
      (K.total (ComplexShape.down ℕ)).homologyπ n x.val := by
    change (K.total (ComplexShape.down ℕ)).homologyπ n (x.val - z.val) = _
    rw [map_sub, horizontalBoundaryCycle_homology, sub_zero]
  rwa [he] at hlow

theorem bicomplex_total_homology_finite_of_secondPage [IsNoetherianRing R] (n : ℕ)
    (hfin : ∀ p j, p + j = n → Module.Finite R ((rowHomologyComplex K j).homology p)) :
    Module.Finite R ((K.total (ComplexShape.down ℕ)).homology n) := by
  have hf : ∀ p, p ≤ n + 1 → (filteredTotalHomology K n p).FG := by
    intro p
    induction p with
    | zero =>
      intro _
      rw [filteredTotalHomology_zero]
      exact Submodule.fg_bot
    | succ p ih =>
      intro hp
      have hpn : p ≤ n := by omega
      let j := n - p
      have hj : p + j = n := by dsimp [j]; omega
      let := hfin p j hj
      let f := boundedTotalSecondPageClass K n p j hj
      let g := ((K.total (ComplexShape.down ℕ)).homologyπ n).hom.comp
        (boundedTotalCycles K n (p + 1)).subtype
      apply integral_range_fg_of_kernel_control f g (filteredTotalHomology K n p)
        (ih (by omega)) (filteredTotalHomology_mono K n (by omega))
      intro x hx
      exact zero_secondPage_class_lowers_filtration K n p j hj x hx
  exact ⟨by rw [← filteredTotalHomology_top K n (n + 1) (by omega)]; exact hf _ le_rfl⟩

end PolycyclicRecognition

end

end OAI
