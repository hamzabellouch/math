import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonalCycles

namespace OAI

/-! # Finite elimination in a first-quadrant bicomplex

Exact rows imply exactness of the finite antidiagonal total complex. The proof
removes the largest horizontal component and terminates after finitely many
columns; no spectral-sequence convergence theorem is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

variable {R : Type} [CommRing R] (K : NatBicomplex R)

theorem diagonal_leading_cycle (n i j : ℕ) (hij : i + j = n)
    (x : bicomplexDiagonal K n) (hx : IsDiagonalCycle K x)
    (hs : ∀ q : ↥(antidiagonal n), i + 1 ≤ q.1.1 → x q = 0) :
    ((K.X i).d j (j - 1)).hom
      (x ⟨(i, j), mem_antidiagonal.mpr hij⟩) = 0 := by
  cases j with
  | zero =>
    have hd : (K.X i).d 0 0 = 0 :=
      (K.X i).shape 0 0 (by simp [ComplexShape.down])
    rw [hd]
    rfl
  | succ j =>
    have he := hx i j (by omega)
    have hh := hs ⟨(i + 1, j), mem_antidiagonal.mpr (by omega)⟩ (by simp)
    rw [hh, map_zero, zero_add] at he
    change ((K.X i).d (j + 1) j).hom
      (x ⟨(i, j + 1), mem_antidiagonal.mpr hij⟩) = 0
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ i) with hu | hu <;>
      simpa [hu, Units.smul_def] using he

theorem diagonal_cycle_bounded_boundary_of_exact_diagonal (n : ℕ)
    (hex : ∀ i j, i + j = n → (K.X i).ExactAt j) (p : ℕ) (x : bicomplexDiagonal K n) (hx : IsDiagonalCycle K x)
    (hs : ∀ q : ↥(antidiagonal n), p ≤ q.1.1 → x q = 0) :
    ∃ y : bicomplexDiagonal K (n + 1), bicomplexDiagonalDifferential K n y = x := by
  classical
  induction p generalizing x with
  | zero =>
    have hz : x = 0 := funext (fun q => hs q (Nat.zero_le _))
    exact ⟨0, by rw [map_zero, hz]⟩
  | succ p ih =>
    by_cases hp : p ≤ n
    · let j := n - p
      have hpn : p + j = n := by dsimp [j]; omega
      let q : ↥(antidiagonal n) := ⟨(p, j), mem_antidiagonal.mpr hpn⟩
      have hcycle : ((K.X p).d j (j - 1)).hom (x q) = 0 :=
        diagonal_leading_cycle K n p j hpn x hx hs
      obtain ⟨y, hy⟩ := row_cycle_lift_of_exactAt K p j (hex p j hpn) (x q) hcycle
      let u : bicomplexDiagonal K (n + 1) :=
        Pi.single (diagonalSucc₂ q) (((-1 : ℤˣ) ^ p)⁻¹ • y)
      have hlead : bicomplexDiagonalDifferential K n u q = x q := by
        rw [diagonalBoundary_single_leading]
        have hm : ((K.X p).d (j + 1) j).hom (((-1 : ℤˣ) ^ p)⁻¹ • y) =
            ((-1 : ℤˣ) ^ p)⁻¹ • ((K.X p).d (j + 1) j).hom y := by
          simp only [Units.smul_def, map_zsmul]
        change (-1 : ℤˣ) ^ p • _ = _
        rw [hm, smul_inv_smul, hy]
      have hres : ∀ r : ↥(antidiagonal n), p ≤ r.1.1 →
          (x - bicomplexDiagonalDifferential K n u) r = 0 := by
        intro r hr
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
          change x r - bicomplexDiagonalDifferential K n u r = 0
          rw [hs r (by omega), diagonalBoundary_single_above K n q _ r hpr, sub_self]
      obtain ⟨v, hv⟩ := ih (x - bicomplexDiagonalDifferential K n u)
        (IsDiagonalCycle.sub K hx (diagonalBoundary_isCycle K n u)) hres
      refine ⟨v + u, ?_⟩
      rw [map_add, hv, sub_add_cancel]
    · apply ih x hx
      intro q hq
      have hn := mem_antidiagonal.mp q.2
      omega

theorem diagonal_cycle_boundary_of_exact_diagonal (n : ℕ)
    (hex : ∀ i j, i + j = n → (K.X i).ExactAt j) (x : bicomplexDiagonal K n) (hx : IsDiagonalCycle K x) :
    ∃ y : bicomplexDiagonal K (n + 1), bicomplexDiagonalDifferential K n y = x := by
  apply diagonal_cycle_bounded_boundary_of_exact_diagonal K n hex (n + 1) x hx
  intro q hq
  have hn := mem_antidiagonal.mp q.2
  omega

theorem diagonal_cycle_bounded_boundary (hex : ∀ i j, (K.X i).ExactAt j)
    (n p : ℕ) (x : bicomplexDiagonal K n) (hx : IsDiagonalCycle K x)
    (hs : ∀ q : ↥(antidiagonal n), p ≤ q.1.1 → x q = 0) :
    ∃ y : bicomplexDiagonal K (n + 1), bicomplexDiagonalDifferential K n y = x :=
  diagonal_cycle_bounded_boundary_of_exact_diagonal K n (fun i j _ => hex i j) p x hx hs

theorem diagonal_cycle_boundary (hex : ∀ i j, (K.X i).ExactAt j)
    (n : ℕ) (x : bicomplexDiagonal K n) (hx : IsDiagonalCycle K x) :
    ∃ y : bicomplexDiagonal K (n + 1), bicomplexDiagonalDifferential K n y = x :=
  diagonal_cycle_boundary_of_exact_diagonal K n (fun i j _ => hex i j) x hx

end PolycyclicRecognition

end

end OAI
