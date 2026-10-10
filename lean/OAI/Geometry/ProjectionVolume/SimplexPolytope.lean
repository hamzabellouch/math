import OAI.Geometry.ProjectionVolume.ProductPolytope
import OAI.Geometry.ProjectionVolume.SimplexNormals

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Paper092

def standardSimplexNormal (d : ℕ) : Option (Fin d) → Euclidean d
  | none => diagonalUnitNormal d
  | some i => -EuclideanSpace.single i (1 : ℝ)

def standardSimplexOffset (d : ℕ) : Option (Fin d) → ℝ
  | none => (Real.sqrt d)⁻¹
  | some _ => 0

theorem standardSimplex_halfspaces (d : ℕ) (hd : 0 < d) :
    {x | ∀ i, ⟪standardSimplexNormal d i, x⟫ ≤ standardSimplexOffset d i} =
      standardSimplex d := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  ext x
  rw [mem_standardSimplex_iff]
  simp [Option.forall, standardSimplexNormal, standardSimplexOffset, diagonalUnitNormal_inner,
    EuclideanSpace.inner_single_left, ← one_div,
    div_le_div_iff_of_pos_right hs, and_comm]

def standardSimplexPolytope (d : ℕ) (hd : 0 < d) : HPolytope d (Option (Fin d)) where
  normal := standardSimplexNormal d
  offset := standardSimplexOffset d
  normal_unit i := by
    cases i with
    | none => exact diagonalUnitNormal_norm d hd
    | some i => simp [standardSimplexNormal]
  compact := by
    rw [standardSimplex_halfspaces d hd]
    exact standardSimplex_isCompact d
  strict_feasible := by
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hc : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    refine ⟨((d : ℝ) + 1)⁻¹ • diagonalVector d, ?_⟩
    intro i
    cases i with
    | none =>
      change ⟪diagonalUnitNormal d, _⟫ < (Real.sqrt d)⁻¹
      rw [diagonalUnitNormal_inner]
      have hsum : (∑ i : Fin d, (((d : ℝ) + 1)⁻¹ • diagonalVector d) i) =
          (d : ℝ) / (d + 1) := by
        simp [diagonalVector, div_eq_mul_inv]
      rw [hsum]
      calc
        _ < 1 / Real.sqrt d := (div_lt_div_iff_of_pos_right hs).mpr
          ((div_lt_one hc).mpr (by linarith))
        _ = _ := one_div _
    | some i =>
      change ⟪-EuclideanSpace.single i (1 : ℝ), _⟫ < 0
      rw [inner_neg_left, EuclideanSpace.inner_single_left]
      simpa [diagonalVector] using neg_neg_of_pos (inv_pos.mpr hc)
  distinct := by
    intro i j h
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        have hh := congrArg (fun q : Euclidean d × ℝ => q.2) h
        change (Real.sqrt d)⁻¹ = 0 at hh
        have hs : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd))
        exact False.elim ((inv_ne_zero hs) hh)
    | some i =>
      cases j with
      | none =>
        have hh := congrArg (fun q : Euclidean d × ℝ => q.2) h
        change 0 = (Real.sqrt d)⁻¹ at hh
        have hs : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd))
        exact False.elim ((inv_ne_zero hs) hh.symm)
      | some j =>
        apply congrArg some
        by_contra hij
        have hh := congrArg (fun q : Euclidean d × ℝ => q.1 i) h
        simp [standardSimplexNormal, hij] at hh

@[simp] theorem standardSimplexPolytope_body (d : ℕ) (hd : 0 < d) :
    (standardSimplexPolytope d hd).body = standardSimplex d :=
  standardSimplex_halfspaces d hd

end Paper092

end

end OAI
