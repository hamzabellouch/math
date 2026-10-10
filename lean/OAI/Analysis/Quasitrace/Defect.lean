import OAI.Analysis.Quasitrace.Extension
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! The fixed positive contraction pair and its uniform real additivity defect. -/

section

namespace Kaplansky
open scoped BigOperators

theorem defect_telescoping (H J u v : ℕ → ℂ) (N : ℕ)
    (h0 : H 0 = 0) (j0 : J 0 = 0) (huv : ∀ i < N, u i = v i) :
    (∑ i ∈ Finset.range N,
      ((H (i+1) - H i - u i) + (-J (i+1) + J i + v i))) = H N - J N := by
  induction N with
  | zero => simp [h0,j0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => huv i (Nat.lt_succ_of_lt hi)),
      huv N (Nat.lt_succ_self N)]
    ring

theorem defect_constant : ((1 : ℝ) - 2/3) / (2*24) = 1/144 := by norm_num

theorem approximation_margin {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ < 1/5) :
    2*δ + δ^2 < 1/2 := by nlinarith [sq_nonneg (δ - 1/5)]

end Kaplansky

end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def partialSum (f : ℕ → A) (i : ℕ) : A := ∑ j ∈ Finset.range i, f j
@[simp] theorem partialSum_zero (f : ℕ → A) : partialSum f 0 = 0 := by simp [partialSum]
theorem partialSum_succ (f : ℕ → A) (i : ℕ) :
    partialSum f (i+1) = partialSum f i + f i := Finset.sum_range_succ f i

theorem partialSum_nonneg (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) (i : ℕ) :
    0 ≤ partialSum f i := Finset.sum_nonneg (fun j _ => hf j)

theorem partialSum_mono (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) {i j : ℕ} (hij : i ≤ j) :
    partialSum f i ≤ partialSum f j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _; exact hf k

theorem term_le_partialSum (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) {i N : ℕ} (hi : i < N) :
    f i ≤ partialSum f N := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_range.mpr hi)

def leftSquare (x : ℕ → A) (i : ℕ) : A := star (x i) * x i
def rightSquare (x : ℕ → A) (i : ℕ) : A := x i * star (x i)

def defectAEntries (x : ℕ → A) (N : ℕ) : Fin N ⊕ Fin N → A :=
  Sum.elim (fun i => partialSum (leftSquare x) i.val)
    (fun i => 1 - partialSum (rightSquare x) i.val)
def defectBEntries (x : ℕ → A) (N : ℕ) : Fin N ⊕ Fin N → A :=
  Sum.elim (fun i => leftSquare x i.val) (fun i => 1 - rightSquare x i.val)
def defectA (x : ℕ → A) (N : ℕ) := diagonal (defectAEntries x N)
def defectB (x : ℕ → A) (N : ℕ) := diagonal (defectBEntries x N)

theorem defect_entries_bounds (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1) :
    (∀ i, 0 ≤ defectAEntries x N i ∧ defectAEntries x N i ≤ 1) ∧
    (∀ i, 0 ≤ defectBEntries x N i ∧ defectBEntries x N i ≤ 1) := by
  have hu : ∀ i, 0 ≤ leftSquare x i := fun i => star_mul_self_nonneg (x i)
  have hv : ∀ i, 0 ≤ rightSquare x i := fun i => mul_star_self_nonneg (x i)
  constructor
  · intro i; cases i with
    | inl i =>
      exact ⟨partialSum_nonneg _ hu _,
        (partialSum_mono _ hu (Nat.le_of_lt i.isLt)).trans_eq hcol⟩
    | inr i =>
      exact ⟨sub_nonneg.mpr ((partialSum_mono _ hv (Nat.le_of_lt i.isLt)).trans hrow),
        sub_le_self _ (partialSum_nonneg _ hv _)⟩
  · intro i; cases i with
    | inl i => exact ⟨hu _, (term_le_partialSum _ hu i.isLt).trans_eq hcol⟩
    | inr i => exact ⟨sub_nonneg.mpr ((term_le_partialSum _ hv i.isLt).trans hrow),
        sub_le_self _ (hv _)⟩

/-- Positivity and the C*-norm contraction condition for the actual pair. -/
theorem defect_pair_positiveContractions (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1) :
    PositiveContraction (defectA x N) ∧ PositiveContraction (defectB x N) := by
  obtain ⟨ha, hb⟩ := defect_entries_bounds x N hcol hrow
  exact ⟨diagonal_positiveContraction _ (fun i => (ha i).1) (fun i => (ha i).2),
    diagonal_positiveContraction _ (fun i => (hb i).1) (fun i => (hb i).2)⟩

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem reflected_defect (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    τ (corner k ((1-a)+(1-b))) - τ (corner k (1-a)) - τ (corner k (1-b)) =
      -τ (corner k (a+b)) + τ (corner k a) + τ (corner k b) := by
  have heq : (1-a)+(1-b) = ((2 : ℝ) : ℂ) • (1 : A) - (a+b) := by
    rw [show ((2 : ℝ) : ℂ) = 1+1 by norm_num, add_smul, one_smul]
    abel
  have ha1 : τ (corner k (1-a)) = τ (corner k (1 : A)) - τ (corner k a) := by
    simpa only [Complex.ofReal_one, one_smul, one_mul] using corner_scalar_sub τ k 1 ha
  have hb1 : τ (corner k (1-b)) = τ (corner k (1 : A)) - τ (corner k b) := by
    simpa only [Complex.ofReal_one, one_smul, one_mul] using corner_scalar_sub τ k 1 hb
  rw [heq, corner_scalar_sub τ k 2 (ha.add hb), ha1, hb1]
  norm_num
  ring

theorem defect_pair_identity (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1)
    (τ : OneQuasitrace (CStarMatrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) A))
    (k : Fin N ⊕ Fin N) :
    τ (defectA x N + defectB x N) - τ (defectA x N) - τ (defectB x N) =
      τ (corner k (1 : A)) - τ (corner k (partialSum (rightSquare x) N)) := by
  obtain ⟨ha,hb⟩ := defect_entries_bounds x N hcol hrow
  have hsum := map_positive_diagonal τ k (defectAEntries x N + defectBEntries x N)
    (fun i => add_nonneg (ha i).1 (hb i).1)
  have hA := map_positive_diagonal τ k (defectAEntries x N) (fun i => (ha i).1)
  have hB := map_positive_diagonal τ k (defectBEntries x N) (fun i => (hb i).1)
  change τ (diagonal (defectAEntries x N) + diagonal (defectBEntries x N)) -
    τ (diagonal (defectAEntries x N)) - τ (diagonal (defectBEntries x N)) = _
  rw [← diagonal_add, hsum, hA, hB, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_sum_type]
  simp only [defectAEntries, defectBEntries, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
  have hreflect (i : Fin N) := reflected_defect τ k (b := rightSquare x i.val)
    ((partialSum_nonneg (rightSquare x) (fun j => mul_star_self_nonneg (x j)) i.val).isSelfAdjoint)
    (IsSelfAdjoint.mul_star_self (x i.val))
  simp_rw [hreflect]
  rw [← Finset.sum_add_distrib]
  have htel := defect_telescoping
    (fun i => τ (corner k (partialSum (leftSquare x) i)))
    (fun i => τ (corner k (partialSum (rightSquare x) i)))
    (fun i => τ (corner k (leftSquare x i)))
    (fun i => τ (corner k (rightSquare x i))) N
    (by simp) (by simp) (fun i _ => corner_square_swap τ k (x i))
  rw [← Fin.sum_univ_eq_sum_range] at htel
  simpa only [partialSum_succ, hcol] using htel

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem scalar_unit_le_one {c : ℝ} (hc : c ≤ 1) : (c : ℂ) • (1 : A) ≤ 1 := by
  simpa only [Complex.coe_smul, one_smul] using
    (smul_le_smul_of_nonneg_right hc (show (0 : A) ≤ 1 from zero_le_one))

theorem uniform_defect (x : ℕ → A) (N : ℕ) (hN : 0 < N) (c : ℝ)
    (_hc0 : 0 ≤ c) (hc : c < 1)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ (c : ℂ) • (1 : A)) :
    PositiveContraction (defectA x N) ∧ PositiveContraction (defectB x N) ∧
    ∀ τ : OneQuasitrace (CStarMatrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) A),
      τ.Normalized → (1-c) / (2*N) ≤
        (τ (defectA x N + defectB x N) - τ (defectA x N) - τ (defectB x N)).re := by
  have hr1 := hrow.trans (scalar_unit_le_one hc.le)
  obtain ⟨ha,hb⟩ := defect_pair_positiveContractions x N hcol hr1
  refine ⟨ha,hb,?_⟩
  intro τ hτ
  let k : Fin N ⊕ Fin N := Sum.inl ⟨0,hN⟩
  rw [defect_pair_identity x N hcol hr1 τ k, Complex.sub_re]
  have hnorm := congrArg Complex.re (corner_normalization τ hτ k)
  have hcard : (Fintype.card (Fin N ⊕ Fin N) : ℂ) = (2*N : ℝ) := by
    simp [two_mul]
  rw [hcard] at hnorm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.one_re] at hnorm
  have hbound := corner_scalar_upper_bound τ k c
    (partialSum_nonneg (rightSquare x) (fun i => mul_star_self_nonneg (x i)) N) hrow
  have hpos : (0 : ℝ) < 2*N := by positivity
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem uniform_defect_twentyFour (x : ℕ → A)
    (hcol : partialSum (leftSquare x) 24 = 1)
    (hrow : partialSum (rightSquare x) 24 ≤ ((2/3 : ℝ) : ℂ) • (1 : A)) :
    PositiveContraction (defectA x 24) ∧ PositiveContraction (defectB x 24) ∧
    ∀ τ : OneQuasitrace (CStarMatrix (Fin 24 ⊕ Fin 24) (Fin 24 ⊕ Fin 24) A),
      τ.Normalized → (1 : ℝ)/144 ≤
        (τ (defectA x 24 + defectB x 24) - τ (defectA x 24) - τ (defectB x 24)).re := by
  simpa only [Nat.cast_ofNat, defect_constant] using
    uniform_defect x 24 (by decide) (2/3) (by norm_num) (by norm_num) hcol hrow

end Kaplansky

end
end

end OAI
