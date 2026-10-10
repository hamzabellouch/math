import OAI.Analysis.WeakInfiniteness.NuclearCoefficients
import OAI.Analysis.WeakInfiniteness.CentralVacuum

namespace OAI

/-! # Finite-level identities for the nuclear approximation of O∞

The shift by a finite set of canonical isometries and its level projections
give the telescoping weights for finite Fock-space compressions.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _
local instance : Module ℝ OInfinity := Module.complexToReal _
local instance : SMulWithZero ℝ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℝ OInfinity _ _
    (@Module.toMulActionWithZero ℝ OInfinity _ _ (Module.complexToReal _))

private lemma finiteCuntz_conjugate_mul (N : ℕ) (a b : OInfinity) (i j : Fin N) :
    (oInfinityIsometry i * a * star (oInfinityIsometry i)) *
      (oInfinityIsometry j * b * star (oInfinityIsometry j)) =
    if i = j then oInfinityIsometry i * (a * b) * star (oInfinityIsometry i) else 0 := by
  have h := oInfinityIsometry_relations (i : ℕ) (j : ℕ)
  by_cases hij : i = j
  · subst j
    simp only [ite_true] at h ⊢
    calc
      _ = oInfinityIsometry i * a *
          (star (oInfinityIsometry i) * oInfinityIsometry i) * b *
          star (oInfinityIsometry i) := by noncomm_ring
      _ = _ := by rw [h]; simp only [mul_one, mul_assoc]
  · have hij' : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
    rw [ite_eq_right hij'] at h
    rw [ite_eq_right hij]
    calc
      _ = oInfinityIsometry i * a *
          (star (oInfinityIsometry i) * oInfinityIsometry j) * b *
          star (oInfinityIsometry j) := by noncomm_ring
      _ = 0 := by rw [h]; simp

def oInfinityFiniteShift (N : ℕ) : OInfinity →⋆ₙₐ[ℂ] OInfinity where
  toFun a := ∑ i : Fin N, oInfinityIsometry i * a * star (oInfinityIsometry i)
  map_zero' := by simp
  map_add' a b := by simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ i : Fin N, oInfinityIsometry i * (c • a) * star (oInfinityIsometry i)) = _
    calc
      _ = ∑ i : Fin N, c • (oInfinityIsometry i * a * star (oInfinityIsometry i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_smul_comm, smul_mul_assoc]
      _ = _ := (Finset.smul_sum (s := Finset.univ) (r := c)
        (f := fun i : Fin N => oInfinityIsometry i * a * star (oInfinityIsometry i))).symm
  map_mul' a b := by
    simp only [Finset.sum_mul, Finset.mul_sum, finiteCuntz_conjugate_mul]
    simp
  map_star' a := by simp only [star_sum, star_mul, star_star, mul_assoc]

def oInfinityLevel (N : ℕ) : ℕ → OInfinity
  | 0 => 1
  | k + 1 => oInfinityFiniteShift N (oInfinityLevel N k)

@[simp] lemma oInfinityLevel_zero (N : ℕ) : oInfinityLevel N 0 = 1 := rfl

@[simp] lemma oInfinityLevel_succ (N k : ℕ) :
    oInfinityLevel N (k + 1) = oInfinityFiniteShift N (oInfinityLevel N k) := rfl

lemma oInfinityLevel_nonneg (N k : ℕ) : 0 ≤ oInfinityLevel N k := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih => exact map_nonneg (oInfinityFiniteShift N) ih

lemma oInfinityLevel_idempotent (N k : ℕ) :
    oInfinityLevel N k * oInfinityLevel N k = oInfinityLevel N k := by
  induction k with
  | zero => exact one_mul _
  | succ k ih =>
    rw [oInfinityLevel_succ, ← map_mul, ih]

lemma oInfinityLevel_antitone (N : ℕ) : Antitone (oInfinityLevel N) := by
  apply antitone_nat_of_succ_le
  intro k
  induction k with
  | zero =>
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (oInfinityLevel_nonneg N 1)).mp
    exact (NonUnitalStarAlgHom.norm_apply_le (oInfinityFiniteShift N) 1).trans
      (by simp)
  | succ k ih =>
    have h := map_nonneg (oInfinityFiniteShift N) (sub_nonneg.mpr ih)
    apply sub_nonneg.mp
    simpa only [map_sub, oInfinityLevel_succ] using h

def oInfinityLevelDifference (N k : ℕ) : OInfinity :=
  oInfinityLevel N k - oInfinityLevel N (k + 1)

lemma oInfinityLevelDifference_nonneg (N k : ℕ) :
    0 ≤ oInfinityLevelDifference N k :=
  sub_nonneg.mpr (oInfinityLevel_antitone N (Nat.le_succ k))

lemma oInfinityLevelDifference_sum (N m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), oInfinityLevelDifference N k =
      1 - oInfinityLevel N (m + 1) := by
  induction m with
  | zero => simp [oInfinityLevelDifference]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold oInfinityLevelDifference
    abel

lemma oInfinityLevel_weighted_sum (N m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), oInfinityLevel N k) +
      (∑ k ∈ Finset.range (m + 1),
        ((m : ℝ) - k) • oInfinityLevelDifference N k) =
      ((m : ℝ) + 1) • (1 : OInfinity) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hweight :
        (∑ k ∈ Finset.range (m + 1),
          (((m : ℝ) + 1) - k) • oInfinityLevelDifference N k) =
        (∑ k ∈ Finset.range (m + 1),
          ((m : ℝ) - k) • oInfinityLevelDifference N k) +
          (1 - oInfinityLevel N (m + 1)) := by
      rw [← oInfinityLevelDifference_sum N m, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      module
    conv_lhs => arg 1; rw [Finset.sum_range_succ]
    conv_lhs => arg 2; rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_smul, add_zero]
    rw [hweight]
    calc
      _ = ((∑ k ∈ Finset.range (m + 1), oInfinityLevel N k) +
          ∑ k ∈ Finset.range (m + 1),
            ((m : ℝ) - k) • oInfinityLevelDifference N k) + 1 := by abel
      _ = _ := by rw [ih]; module

end WeakPureInfiniteness

end

end OAI
