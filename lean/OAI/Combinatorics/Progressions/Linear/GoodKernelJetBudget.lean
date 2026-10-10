import OAI.Combinatorics.Progressions.Lattices.IntegerAffineResidues
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget

namespace OAI

section

namespace Erdos3

theorem goodScalarKernelTuple_index_le_exp {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L B : ℕ} {H κ : ℝ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple s κ B x)
    (hB : (B : ℝ) ≤ Real.exp H) :
    ((scalarCubeDifferenceMatrix x).mulVecLin.range.toAddSubgroup.index : ℝ) ≤
      Real.exp (Fintype.card I * H) := by
  have hi := hasBoundedScalarPeriod_index_le (scalarCubeDifferenceMatrix x).mulVecLin.range B hx.2
  calc
    _ ≤ (B : ℝ)^Fintype.card I := by exact_mod_cast hi
    _ ≤ (Real.exp H)^Fintype.card I := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem goodScalarKernelTuple_period_powers_le_exp {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L B : ℕ} {H κ : ℝ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple s κ B x)
    (hB : (B : ℝ) ≤ Real.exp H) :
    ∃ a : ℕ, 0 < a ∧ a ≤ B ∧
      integerScalarLattice I (a : ℤ) ≤ (scalarCubeDifferenceMatrix x).mulVecLin.range ∧
      ∀ h : ℕ, ((a^h : ℕ) : ℝ) ≤ Real.exp (h * H) := by
  obtain ⟨a, ha, haB, hperiod⟩ := hx.2
  refine ⟨a, ha, haB, hperiod, fun h => ?_⟩
  have haR : (a : ℝ) ≤ Real.exp H := (by exact_mod_cast haB : (a : ℝ) ≤ B).trans hB
  push_cast
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) haR h).trans_eq (Real.exp_nat_mul _ _).symm

theorem goodScalarKernelTuple_inverse_le_exp {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L B : ℕ} {H : ℝ}
    (hL : 0 < L) (hBpos : 0 < B) (s : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hB : (B : ℝ) ≤ Real.exp H) :
    (matrixSupCLM (normalizedScalarCubePivot s x)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedScalarCubePivot s x)).inverse‖ ≤
        Real.exp (Fintype.card I + (Fintype.card I : ℝ)^2 + H) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hBpos
  obtain ⟨hinv, hnorm⟩ := goodScalarKernelTuple_pivot_inverse hL s (1 / (B : ℝ)) B
    (one_div_pos.mpr hBp) x hx
  refine ⟨hinv, hnorm.trans ?_⟩
  rw [one_div, div_inv_eq_mul]
  have hq : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp ((Fintype.card I : ℝ)^2) * Real.exp H := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

theorem goodScalarKernelTuple_jet_budget {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] {L B : ℕ} {H κ : ℝ}
    (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (hB : (B : ℝ) ≤ Real.exp H)
    (root : J → ℤ) (s : ℕ) :
    ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ ((a^s : ℕ) : ℝ) ≤ Real.exp (s * H) ∧
      ∀ (h : ℕ), h ≤ s → ∀ (rows : O → Finset I), Function.Injective rows →
        (∀ o, (rows o).card ≤ h) →
        integerScalarLattice O ((a^s : ℕ) : ℤ) ≤
          (boundedDegreeIntegerJetMatrix root (scalarCubeDifferenceMatrix x) h rows).mulVecLin.range ∧
        ((boundedDegreeIntegerJetMatrix root (scalarCubeDifferenceMatrix x) h rows).mulVecLin.range.toAddSubgroup.index : ℝ) ≤
          Real.exp (Fintype.card O * (s * H)) := by
  obtain ⟨a, ha, haB, hperiod, hpowers⟩ := goodScalarKernelTuple_period_powers_le_exp selection x hx hB
  refine ⟨a, ha, haB, hpowers s, fun h hh rows hinj hdegree => ?_⟩
  have hp := boundedDegreeIntegerJetMatrix_common_period root (scalarCubeDifferenceMatrix x)
    (a : ℤ) hperiod s h hh rows hinj hdegree
  rw [← Nat.cast_pow] at hp
  refine ⟨hp, ?_⟩
  let : NeZero (a^s) := ⟨(Nat.pow_pos ha).ne'⟩
  have hi := residueLatticeImage_index_le
    (boundedDegreeIntegerJetMatrix root (scalarCubeDifferenceMatrix x) h rows).mulVecLin.range (a^s) hp
  calc
    _ ≤ (((a^s : ℕ) : ℝ)^Fintype.card O) := by exact_mod_cast hi
    _ ≤ (Real.exp (s * H))^Fintype.card O := pow_le_pow_left₀ (Nat.cast_nonneg _) (hpowers s) _
    _ = _ := (Real.exp_nat_mul _ _).symm

end Erdos3

end

end OAI
