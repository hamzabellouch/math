import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexFilteredHomology
import Mathlib.RingTheory.Finiteness.Cofinite

namespace OAI

/-! # Finiteness from the finite diagonal of row homology

Only the row homology groups on the selected diagonal need be finite. The
proof uses the actual total-homology filtration and lowers support by an
actual boundary when a leading class vanishes.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module Submodule.Quotient.module

variable {R : Type} [CommRing R]

theorem integral_range_fg_of_kernel_control [IsNoetherianRing R]
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] [Module.Finite R B]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C) (S : Submodule R C)
    (hS : S.FG) (hSg : S ≤ LinearMap.range g)
    (hker : ∀ x, f x = 0 → g x ∈ S) : (LinearMap.range g).FG := by
  have hle : LinearMap.ker f ≤ LinearMap.ker (S.mkQ.comp g) := by
    intro x hx
    change S.mkQ (g x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hker x hx)
  have hq : (LinearMap.range (S.mkQ.comp g)).FG :=
    Submodule.range_fg_iff_ker_cofg.mpr ((Submodule.CoFG.ker f).of_le hle)
  apply Submodule.fg_of_fg_map_of_fg_inf_ker S.mkQ
  · simpa only [LinearMap.range_comp] using hq
  · simpa only [Submodule.ker_mkQ, inf_eq_right.mpr hSg] using hS

variable (K : NatBicomplex R)

theorem filteredTotalHomology_mono (n : ℕ) {p q : ℕ} (h : p ≤ q) :
    filteredTotalHomology K n p ≤ filteredTotalHomology K n q := by
  rintro a ⟨x, rfl⟩
  refine ⟨⟨x.val, ?_⟩, rfl⟩
  apply (mem_boundedTotalCycles K n q _).mpr
  intro r hr
  exact boundedTotalCycles_support K n p x r (h.trans hr)

theorem filteredTotalHomology_zero (n : ℕ) : filteredTotalHomology K n 0 = ⊥ := by
  apply bot_unique
  rintro a ⟨x, rfl⟩
  have hx : x.val = 0 := by
    apply (ModuleCat.mono_iff_injective ((K.total (ComplexShape.down ℕ)).iCycles n)).mp
      inferInstance
    apply (bicomplexDiagonalEquiv K n).injective
    funext r
    exact (boundedTotalCycles_support K n 0 x r (Nat.zero_le _)).trans (by simp)
  change (K.total (ComplexShape.down ℕ)).homologyπ n x.val = 0
  rw [hx, map_zero]

theorem filteredTotalHomology_top (n p : ℕ) (h : n < p) :
    filteredTotalHomology K n p = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((K.total (ComplexShape.down ℕ)).homologyπ n)).mp inferInstance a
  refine ⟨⟨x, ?_⟩, rfl⟩
  apply (mem_boundedTotalCycles K n p _).mpr
  intro r hr
  have hn := mem_antidiagonal.mp r.2
  omega

theorem bicomplex_total_homology_finite_of_diagonal [IsNoetherianRing R] (n : ℕ)
    (hfin : ∀ i j, i + j = n → Module.Finite R ((K.X i).homology j)) :
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
      let f := boundedTotalLeadingHomology K n p j hj
      let g := ((K.total (ComplexShape.down ℕ)).homologyπ n).hom.comp
        (boundedTotalCycles K n (p + 1)).subtype
      apply integral_range_fg_of_kernel_control f g (filteredTotalHomology K n p)
        (ih (by omega)) (filteredTotalHomology_mono K n (by omega))
      intro x hx
      exact zero_leading_class_lowers_filtration K n p j hj x hx
  exact ⟨by rw [← filteredTotalHomology_top K n (n + 1) (by omega)]; exact hf _ le_rfl⟩

end PolycyclicRecognition

end

end OAI
