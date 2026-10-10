import OAI.NumberTheory.DukePrimeDegree.Geometry.DyadicBoundaryCuts
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogProper

namespace OAI

/-! # Proper radial heights with controlled boundary strips

Well-separated radial thresholds can be chosen with one common strip
bound. The corresponding integer height is proper and has unit jumps
under the prescribed right translation.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_controlled_radial_height {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ] (a : G n) :
    ∃ (B : ℝ) (t : ℕ → ℝ) (H : X n → ℕ),
      0 < B ∧ matrixLogLength a < B ∧ Measurable H ∧
      (∀ m : ℕ, B*(2*(m:ℝ)+1/2) < t m ∧ t m < B*(2*(m:ℝ)+1)) ∧
      (∀ m, {x | H x ≤ m} =
        {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t m}) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1) ∧
      ∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x=t m}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip
          (quotientLogDistance (Quotient.mk _ (1 : G n))) (t m) ((1/4:ℝ)^k)) ≤
            ENNReal.ofReal (16/B*(1/2:ℝ)^k) := by
  classical
  let B := 1+matrixLogLength a
  have hB : 0 < B := by dsimp [B]; linarith [matrixLogLength_nonneg a]
  have hBa : matrixLogLength a < B := by dsimp [B]; linarith
  let D : X n → ℝ := quotientLogDistance (Quotient.mk _ (1 : G n))
  have hD : Continuous D := continuous_quotientLogDistance n _
  have hex (m : ℕ) := exists_dyadic_boundary_cut μ hD.measurable
    (show B*(2*(m:ℝ)+1/2) < B*(2*(m:ℝ)+1) by nlinarith)
  choose t ht hnull hboundary using hex
  have hgap (m : ℕ) : t m+B ≤ t (m+1) := by
    have h₁ := (ht m).2
    have h₂ := (ht (m+1)).1
    push_cast at h₂
    nlinarith
  have hmono : Monotone t := monotone_nat_of_le_succ fun m => by
    have := hgap m
    linarith
  have hfinite (x : X n) : ∃ m : ℕ, D x ≤ t m := by
    obtain ⟨m,hm⟩ := exists_nat_gt (D x/B)
    have hx : D x < (m:ℝ)*B := (div_lt_iff₀ hB).mp hm
    refine ⟨m,?_⟩
    have ht₀ := (ht m).1
    have hm₀ : 0 ≤ B*(m:ℝ) := mul_nonneg hB.le (Nat.cast_nonneg _)
    linarith
  let H : X n → ℕ := fun x => Nat.find (hfinite x)
  have hle (x : X n) (m : ℕ) : H x ≤ m ↔ D x ≤ t m := by
    constructor
    · intro h
      exact (Nat.find_spec (hfinite x)).trans (hmono h)
    · exact Nat.find_min' (hfinite x)
  have hsets (m : ℕ) : {x | H x ≤ m} = {x | D x ≤ t m} := Set.ext fun x => hle x m
  have hHm : Measurable H := by
    apply measurable_of_Iic
    intro m
    change MeasurableSet {x | H x ≤ m}
    rw [hsets]
    exact measurableSet_le hD.measurable measurable_const
  refine ⟨B,t,H,hB,hBa,hHm,ht,hsets,?_,?_,?_⟩
  · intro m
    rw [hsets]
    exact isCompact_quotientLogDistance_sublevel _ _
  · intro x
    obtain ⟨hlo,hhi⟩ := abs_le.mp (quotientLogDistance_right_bound
      (Quotient.mk _ (1 : G n)) x a)
    have hx := (hle x (H x)).mp le_rfl
    have hax := (hle (rightAction x a) (H (rightAction x a))).mp le_rfl
    constructor
    · apply (hle _ _).mpr
      have hg := hgap (H x)
      change D (rightAction x a)-D x ≤ matrixLogLength a at hhi
      linarith
    · apply (hle _ _).mpr
      have hg := hgap (H (rightAction x a))
      change -matrixLogLength a ≤ D (rightAction x a)-D x at hlo
      linarith
  · intro m
    refine ⟨hnull m,?_⟩
    intro k
    convert hboundary m k using 1
    congr 1
    field_simp [hB.ne']
    ring

end DukePrimeDegree

end

end OAI
