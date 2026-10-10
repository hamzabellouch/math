import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralMatrixFiniteOrder
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! # A uniform bound for finite faithful rational representations

The integral lattice is the span of the finite orbit of a rational basis.
Reduction modulo three then bounds the group order.
-/
noncomputable section
namespace PolycyclicRecognition
open Module
variable {G V I : Type} [Group G] [Finite G]
  [AddCommGroup V] [Module ℚ V] [Fintype I]

def finiteOrbitIntegerLattice (ρ : G →* Module.End ℚ V) (b : Basis I ℚ V) :
    Submodule ℤ V := Submodule.span ℤ (Set.range fun p : G × I => ρ p.1 (b p.2))

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerLattice_basis_mem (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) (i : I) : b i ∈ finiteOrbitIntegerLattice ρ b := by
  apply Submodule.subset_span
  exact ⟨(1, i), by simp⟩

theorem finiteOrbitIntegerLattice_isLattice (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) : Submodule.IsLattice ℚ (finiteOrbitIntegerLattice ρ b) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact Submodule.subset_span (finiteOrbitIntegerLattice_basis_mem ρ b i)

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerLattice_stable (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) (g : G) {v : V} (hv : v ∈ finiteOrbitIntegerLattice ρ b) :
    ρ g v ∈ finiteOrbitIntegerLattice ρ b := by
  let f := (ρ g).restrictScalars ℤ
  change f v ∈ finiteOrbitIntegerLattice ρ b
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    simp [f, map_mul, Module.End.mul_apply]
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (finiteOrbitIntegerLattice ρ b).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (finiteOrbitIntegerLattice ρ b).smul_mem a hx

def finiteOrbitIntegerRepresentation (ρ : G →* Module.End ℚ V) (b : Basis I ℚ V) :
    G →* Module.End ℤ (finiteOrbitIntegerLattice ρ b) where
  toFun g :=
    { toFun v := ⟨ρ g v, finiteOrbitIntegerLattice_stable ρ b g v.property⟩
      map_add' x y := Subtype.ext (map_add (ρ g) (x : V) (y : V))
      map_smul' a v := Subtype.ext ((ρ g).restrictScalars ℤ |>.map_smul a (v : V)) }
  map_one' := by ext v; exact congrArg (fun f : Module.End ℚ V => f v) ρ.map_one
  map_mul' g h := by ext v; exact congrArg (fun f : Module.End ℚ V => f v) (ρ.map_mul g h)

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerRepresentation_injective (ρ : G →* Module.End ℚ V)
    (hρ : Function.Injective ρ) (b : Basis I ℚ V) :
    Function.Injective (finiteOrbitIntegerRepresentation ρ b) := by
  intro g h he
  apply hρ
  apply b.ext
  intro i
  exact congrArg (fun f : Module.End ℤ (finiteOrbitIntegerLattice ρ b) =>
    (f ⟨b i, finiteOrbitIntegerLattice_basis_mem ρ b i⟩ : V)) he

theorem finite_rational_representation_card_le [Module.Finite ℚ V]
    (ρ : G →* Module.End ℚ V) (hρ : Function.Injective ρ) :
    Nat.card G ≤ 3 ^ (Module.finrank ℚ V * Module.finrank ℚ V) := by
  classical
  let b := Module.Free.chooseBasis ℚ V
  let L := finiteOrbitIntegerLattice ρ b
  let : Submodule.IsLattice ℚ L := finiteOrbitIntegerLattice_isLattice ρ b
  let c := Module.Free.chooseBasis ℤ L
  let σ : G →* Matrix (Module.Free.ChooseBasisIndex ℤ L)
      (Module.Free.ChooseBasisIndex ℤ L) ℤ :=
    (LinearMap.toMatrixAlgEquiv c).toMonoidHom.comp (finiteOrbitIntegerRepresentation ρ b)
  have hσ : Function.Injective σ :=
    (LinearMap.toMatrixAlgEquiv c).injective.comp (finiteOrbitIntegerRepresentation_injective ρ hρ b)
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ V := by
    rw [← Module.finrank_eq_card_basis c]
    exact congrArg Cardinal.toNat (Submodule.IsLattice.rank' ℚ L)
  simpa only [hc] using finite_integral_matrix_representation_card_le σ hσ

end PolycyclicRecognition

end

end OAI
