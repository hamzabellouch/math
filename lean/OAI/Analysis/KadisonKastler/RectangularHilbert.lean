import OAI.Analysis.KadisonKastler.HilbertMatrix

namespace OAI

/-! # Rectangular operator matrices on finite Hilbert sums -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m n : Type*} [Fintype m] [Fintype n]

local instance rectangularHilbertOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rectangularHilbertOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def rectangularHilbertMatrix (M : CStarMatrix m n (H →L[ℂ] H)) :
    Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert m H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : m => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (PiLp.proj 2 (fun _ : n => H) j)))

omit [CompleteSpace H] [Fintype m] in
@[simp]
theorem rectangularHilbertMatrix_apply (M : CStarMatrix m n (H →L[ℂ] H))
    (x : Generator.FiniteHilbert n H) (i : m) :
    rectangularHilbertMatrix M x i = ∑ j, M i j (x j) := by
  simp [rectangularHilbertMatrix]

def hilbertExtendLeft (x : Generator.FiniteHilbert m H) : Generator.FiniteHilbert (m ⊕ n) H :=
  WithLp.toLp 2 (Sum.elim x fun _ => 0)

def hilbertExtendRight (x : Generator.FiniteHilbert n H) : Generator.FiniteHilbert (m ⊕ n) H :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) x)

def hilbertRestrictRight (x : Generator.FiniteHilbert (m ⊕ n) H) : Generator.FiniteHilbert n H :=
  WithLp.toLp 2 (fun i => x (Sum.inr i))

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
@[simp]
theorem norm_hilbertExtendLeft (x : Generator.FiniteHilbert m H) :
    ‖hilbertExtendLeft (n := n) x‖ = ‖x‖ := by
  simp [PiLp.norm_eq_of_L2, hilbertExtendLeft, Fintype.sum_sum_type]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
@[simp]
theorem norm_hilbertExtendRight (x : Generator.FiniteHilbert n H) :
    ‖hilbertExtendRight (m := m) x‖ = ‖x‖ := by
  simp [PiLp.norm_eq_of_L2, hilbertExtendRight, Fintype.sum_sum_type]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem norm_hilbertRestrictRight_le (x : Generator.FiniteHilbert (m ⊕ n) H) :
    ‖hilbertRestrictRight x‖ ≤ ‖x‖ := by
  simp only [PiLp.norm_eq_of_L2, hilbertRestrictRight,
    Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem hilbertMatrix_rectangularCorner [DecidableEq m] [DecidableEq n]
    (M : CStarMatrix m n (H →L[ℂ] H)) (x : Generator.FiniteHilbert (m ⊕ n) H) :
    hilbertMatrix (rectangularCorner M) x =
      hilbertExtendLeft (rectangularHilbertMatrix M (hilbertRestrictRight x)) := by
  ext i
  rcases i with i | i <;>
    simp [hilbertMatrix_apply, rectangularCorner, rectangularHilbertMatrix_apply,
      hilbertExtendLeft, hilbertRestrictRight, Fintype.sum_sum_type]

/-- The rectangular C⋆-matrix norm is its actual Hilbert-space operator norm. -/
theorem norm_rectangularHilbertMatrix (M : CStarMatrix m n (H →L[ℂ] H)) :
    ‖rectangularHilbertMatrix M‖ = ‖M‖ := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (hilbertMatrix (rectangularCorner M)).le_opNorm
      (hilbertExtendRight (m := m) x)
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft, norm_hilbertMatrix,
      norm_rectangularCorner, norm_hilbertExtendRight] at h
    simpa only [hilbertRestrictRight, hilbertExtendRight, Sum.elim_inr,
      WithLp.toLp_ofLp] using h
  · rw [← norm_rectangularCorner M, ← norm_hilbertMatrix]
    apply (hilbertMatrix (rectangularCorner M)).opNorm_le_bound
      (norm_nonneg (rectangularHilbertMatrix M))
    intro x
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft]
    exact (rectangularHilbertMatrix M).le_opNorm (hilbertRestrictRight x) |>.trans
      (mul_le_mul_of_nonneg_left (norm_hilbertRestrictRight_le x) (norm_nonneg _))

omit [CompleteSpace H] in
@[simp]
theorem norm_tupleSingle [DecidableEq n] (i : n) (x : H) :
    ‖Generator.tupleSingle i x‖ = ‖x‖ := by
  change ‖PiLp.single (β := fun _ : n => H) 2 i x‖ = ‖x‖
  exact PiLp.norm_single 2 (fun _ : n => H) i x

omit [CompleteSpace H] in
/-- Passing to one coordinate in each member of a Hilbert tuple is contractive. -/
theorem norm_hilbertTuple_coordinate_le {W : Submodule ℂ (Generator.FiniteHilbert n H)}
    (i : n) (x : Generator.FiniteHilbert m W) :
    ‖WithLp.toLp 2 (fun j => ((x j : W) : Generator.FiniteHilbert n H) i)‖ ≤ ‖x‖ := by
  simp only [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ((x j).val) i) 2

end

end KadisonKastler

end OAI
