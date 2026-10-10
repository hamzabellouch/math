import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexTotalExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyBoundary

namespace OAI

/-! # The finite column filtration on actual total homology

A cycle with zero leading row class can be changed by an actual total boundary
so that its support lies in fewer columns. This is the elementary filtration
step used for finiteness, without identifying a nilpotent group's homology
with the exterior algebra of its abelianization.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module
variable {R : Type} [CommRing R] (K : NatBicomplex R)

/-- Actual total cycles supported in columns strictly below `p`. -/
def boundedTotalCycles (n p : ℕ) :
    Submodule R ((K.total (ComplexShape.down ℕ)).cycles n) :=
  ⨅ q : ↥(antidiagonal n), ⨅ (_ : p ≤ q.1.1),
    LinearMap.ker ((LinearMap.proj q).comp ((bicomplexToDiagonal K n).comp
      ((K.total (ComplexShape.down ℕ)).iCycles n).hom))

@[simp] theorem mem_boundedTotalCycles (n p : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).cycles n) :
    x ∈ boundedTotalCycles K n p ↔ ∀ q : ↥(antidiagonal n), p ≤ q.1.1 →
      bicomplexToDiagonal K n ((K.total (ComplexShape.down ℕ)).iCycles n x) q = 0 := by
  simp [boundedTotalCycles]

theorem boundedTotalCycles_support (n p : ℕ) (x : boundedTotalCycles K n p)
    (q : ↥(antidiagonal n)) (hq : p ≤ q.1.1) :
    bicomplexToDiagonal K n ((K.total (ComplexShape.down ℕ)).iCycles n x.val) q = 0 :=
  (mem_boundedTotalCycles K n p x.val).mp x.property q hq

/-- The induced filtration on the homology of the given total complex. -/
def filteredTotalHomology (n p : ℕ) :
    Submodule R ((K.total (ComplexShape.down ℕ)).homology n) :=
  LinearMap.range (((K.total (ComplexShape.down ℕ)).homologyπ n).hom.comp
    (boundedTotalCycles K n p).subtype)

theorem totalCycles_isDiagonalCycle (n : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).cycles n) :
    IsDiagonalCycle K (bicomplexToDiagonal K n
      ((K.total (ComplexShape.down ℕ)).iCycles n x)) := by
  apply totalCycle_toDiagonal
  exact congrArg (fun f => f x) ((K.total (ComplexShape.down ℕ)).iCycles_d n (n - 1))

/-- The leading component as a map to the cycles in its row. -/
def boundedTotalLeadingCycles (n p j : ℕ) (h : p + j = n) :
    ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶ (K.X p).cycles j := by
  let q : ↥(antidiagonal n) := ⟨(p, j), mem_antidiagonal.mpr h⟩
  let f : ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶ (K.X p).X j :=
    ModuleCat.ofHom (((LinearMap.proj q).comp (bicomplexToDiagonal K n)).comp
      (((K.total (ComplexShape.down ℕ)).iCycles n).hom.comp
        (boundedTotalCycles K n (p + 1)).subtype))
  have hn : (ComplexShape.down ℕ).next j = j - 1 := by
    cases j with
    | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intros; simp [ComplexShape.down])
    | succ j => exact (ComplexShape.down ℕ).next_eq' rfl
  apply (K.X p).liftCycles f (j - 1) hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact diagonal_leading_cycle K n p j h _ (totalCycles_isDiagonalCycle K n x.val)
    (boundedTotalCycles_support K n (p + 1) x)

theorem boundedTotalLeadingCycles_apply (n p j : ℕ) (h : p + j = n)
    (x : boundedTotalCycles K n (p + 1)) :
    (K.X p).iCycles j (boundedTotalLeadingCycles K n p j h x) =
      bicomplexToDiagonal K n ((K.total (ComplexShape.down ℕ)).iCycles n x.val)
        ⟨(p, j), mem_antidiagonal.mpr h⟩ := by
  let q : ↥(antidiagonal n) := ⟨(p, j), mem_antidiagonal.mpr h⟩
  let f : ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶ (K.X p).X j :=
    ModuleCat.ofHom (((LinearMap.proj q).comp (bicomplexToDiagonal K n)).comp
      (((K.total (ComplexShape.down ℕ)).iCycles n).hom.comp
        (boundedTotalCycles K n (p + 1)).subtype))
  have he : boundedTotalLeadingCycles K n p j h ≫ (K.X p).iCycles j = f := by
    unfold boundedTotalLeadingCycles
    exact (K.X p).liftCycles_i _ _ _ _
  exact congrArg (fun t : ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶
    (K.X p).X j => t.hom x) he

/-- The leading row's homology class. -/
def boundedTotalLeadingHomology (n p j : ℕ) (h : p + j = n) :
    boundedTotalCycles K n (p + 1) →ₗ[R] (K.X p).homology j :=
  ((K.X p).homologyπ j).hom.comp (boundedTotalLeadingCycles K n p j h).hom

theorem zero_leading_class_lowers_filtration (n p j : ℕ) (h : p + j = n)
    (x : boundedTotalCycles K n (p + 1))
    (hx : boundedTotalLeadingHomology K n p j h x = 0) :
    (K.total (ComplexShape.down ℕ)).homologyπ n x.val ∈ filteredTotalHomology K n p := by
  classical
  let T := K.total (ComplexShape.down ℕ)
  let q : ↥(antidiagonal n) := ⟨(p, j), mem_antidiagonal.mpr h⟩
  let v := bicomplexToDiagonal K n (T.iCycles n x.val)
  obtain ⟨w, hw⟩ := exists_boundary_of_homologyπ_eq_zero (K.X p) j
    (boundedTotalLeadingCycles K n p j h x) hx
  rw [boundedTotalLeadingCycles_apply] at hw
  let u : bicomplexDiagonal K (n + 1) :=
    Pi.single (diagonalSucc₂ q) (((-1 : ℤˣ) ^ p)⁻¹ • w)
  have hlead : bicomplexDiagonalDifferential K n u q = v q := by
    rw [diagonalBoundary_single_leading]
    have hm : ((K.X p).d (j + 1) j).hom (((-1 : ℤˣ) ^ p)⁻¹ • w) =
        ((-1 : ℤˣ) ^ p)⁻¹ • ((K.X p).d (j + 1) j).hom w := by
      simp only [Units.smul_def, map_zsmul]
    change (-1 : ℤˣ) ^ p • _ = _
    rw [hm, smul_inv_smul, hw]
  let z : T.cycles n := T.toCycles (n + 1) n (bicomplexFromDiagonal K (n + 1) u)
  have hz : bicomplexToDiagonal K n (T.iCycles n z) =
      bicomplexDiagonalDifferential K n u := by
    change bicomplexToDiagonal K n
      ((T.iCycles n) (T.toCycles (n + 1) n _)) = _
    rw [show (T.iCycles n) (T.toCycles (n + 1) n _) =
      (T.d (n + 1) n) (bicomplexFromDiagonal K (n + 1) u) from
        congrArg (fun f => f (bicomplexFromDiagonal K (n + 1) u)) (T.toCycles_i (n + 1) n)]
    rfl
  have hs : x.val - z ∈ boundedTotalCycles K n p := by
    apply (mem_boundedTotalCycles K n p _).mpr
    intro r hr
    change bicomplexToDiagonal K n (T.iCycles n (x.val - z)) r = 0
    simp only [map_sub, Pi.sub_apply, hz]
    by_cases he : r.1.1 = p
    · have hrq : r = q := by
        apply Subtype.ext
        apply Prod.ext
        · exact he
        · have hn := mem_antidiagonal.mp r.2
          dsimp [q]
          omega
      subst r
      exact sub_eq_zero.mpr hlead.symm
    · have hpr : p < r.1.1 := by omega
      rw [boundedTotalCycles_support K n (p + 1) x r (by omega), diagonalBoundary_single_above K n q _ r hpr, sub_self]
  change ∃ y : boundedTotalCycles K n p, T.homologyπ n y.val = T.homologyπ n x.val
  refine ⟨⟨x.val - z, hs⟩, ?_⟩
  change T.homologyπ n (x.val - z) = T.homologyπ n x.val
  rw [map_sub]
  have hp : T.homologyπ n z = 0 :=
    congrArg (fun f => f (bicomplexFromDiagonal K (n + 1) u))
      (T.toCycles_comp_homologyπ (n + 1) n)
  rw [hp, sub_zero]

end PolycyclicRecognition

end

end OAI
