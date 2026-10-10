import OAI.Combinatorics.BalancedRyser.Local.LocalPrecoverageTransport

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem offsetProbability_eq_expect (E : MergedPairs F → Prop) :
    offsetProbability E = 𝔼 M, if E M then (1 : ℝ) else 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  rfl

omit [Field F] in

theorem bool_pair_expect (s : Bool) (v w : F) :
    (𝔼 o : Bool → F, if o s = v ∧ o (!s) = w then (1 : ℝ) else 0) =
      (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  let f : Bool → F := fun t => if t = s then v else w
  have hiff (o : Bool → F) : (o s = v ∧ o (!s) = w) ↔ o = f := by
    constructor
    · intro h
      funext t
      cases s <;> cases t <;> simp_all [f]
    · rintro rfl
      cases s <;> simp [f]
  simp_rw [hiff]
  rw [Fintype.expect_eq_sum_div_card]
  simp [one_div, inv_pow]

theorem two_offset_factorization (d : Direction F) (s : Bool)
    (A : MergedPairs F → Prop) (v w : MergedPairs F → F)
    (hA : ∀ M o, A (Function.update M d o) ↔ A M)
    (hv : ∀ M o, v (Function.update M d o) = v M)
    (hw : ∀ M o, w (Function.update M d o) = w M) :
    offsetProbability (fun M => A M ∧ M d s = v M ∧ M d (!s) = w M) =
      offsetProbability A * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  rw [offsetProbability_eq_expect, offsetProbability_eq_expect]
  trans (𝔼 M : MergedPairs F, 𝔼 o : Bool → F,
    if A (Function.update M d o) ∧
      (Function.update M d o) d s = v (Function.update M d o) ∧
      (Function.update M d o) d (!s) = w (Function.update M d o) then (1 : ℝ) else 0)
  · convert (DependencyExtraction.expect_coordinate_refresh
      (α := Direction F) (β := Bool → F) d
      (fun M => if A M ∧ M d s = v M ∧ M d (!s) = w M then (1 : ℝ) else 0)).symm using 1
    apply Finset.expect_congr rfl
    intro M _
    split_ifs <;> rfl
  calc
    (𝔼 M, 𝔼 o, if A (Function.update M d o) ∧
        (Function.update M d o) d s = v (Function.update M d o) ∧
        (Function.update M d o) d (!s) = w (Function.update M d o) then (1 : ℝ) else 0) =
        𝔼 M, (if A M then (1 : ℝ) else 0) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
      apply Finset.expect_congr rfl
      intro M _
      simp_rw [hA, hv, hw, Function.update_self]
      by_cases h : A M
      · simp only [h, true_and, ite_true, one_mul]
        exact bool_pair_expect s (v M) (w M)
      · simp [h]
    _ = _ := (Finset.expect_mul _ _ _).symm

variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

omit [Fintype F] in

theorem prescribedPoint_eq_of_used_agreement (M N : MergedPairs F)
    (hMN : ∀ d ∈ Finset.univ.image a.2, M d = N d) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M ij = prescribedPoint P a bits N ij := by
  have hleft := hMN (a.2 (P.classOf ij.1 ij.2))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 ij.2, Finset.mem_univ _, rfl⟩)
  have hright := hMN (a.2 (P.classOf ij.1 (ij.2 + 1)))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 (ij.2 + 1), Finset.mem_univ _, rfl⟩)
  simp only [prescribedPoint, tuplePoint, prescribedTuple, constituent, hleft, hright]

theorem prescribedPoint_refresh_unused (d : Direction F)
    (hd : d ∈ unusedDirections a) (M : MergedPairs F) (o : Bool → F)
    (ij : Fin b × Fin 4) :
    prescribedPoint P a bits (Function.update M d o) ij = prescribedPoint P a bits M ij := by
  apply prescribedPoint_eq_of_used_agreement
  intro e he
  apply Function.update_of_ne
  intro hed
  exact (mem_unusedDirections d).mp hd (hed ▸ he)

theorem aligned_refresh_unused (d : Direction F) (hd : d ∈ unusedDirections a)
    (M : MergedPairs F) (o : Bool → F) :
    Aligned P a bits p (Function.update M d o) ↔ Aligned P a bits p M := by
  simp only [Aligned, prescribedPoint_refresh_unused d hd M o]

theorem aligned_partner_incidence_probability (d : Direction F)
    (hd : d ∈ unusedDirections a) (s : Bool) (ij : Fin b × Fin 4) :
    offsetProbability (fun M => Aligned P a bits p M ∧
      OnLine p (constituent M d s) ∧
      OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))) =
      offsetProbability (Aligned P a bits p) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  have h := two_offset_factorization d s (Aligned P a bits p)
    (fun _ => lineEval d p) (fun M => lineEval d (prescribedPoint P a bits M ij))
    (aligned_refresh_unused d hd) (fun _ _ => rfl)
    (fun M o => congrArg (lineEval d) (prescribedPoint_refresh_unused d hd M o ij))
  simpa only [OnLine, constituent, eq_comm] using h

theorem offsetProbability_nonneg (E : MergedPairs F → Prop) :
    0 ≤ offsetProbability E := by
  unfold offsetProbability
  positivity

omit [Field F] in

theorem offsetProbability_exists_le_sum {ι : Type*} [Fintype ι]
    (E : ι → MergedPairs F → Prop) :
    offsetProbability (fun M => ∃ i, E i M) ≤ ∑ i, offsetProbability (E i) := by
  simp_rw [offsetProbability_eq_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro M _
  by_cases h : ∃ i, E i M
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      (1 : ℝ) = if E i M then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if E j M then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if E j M then (1 : ℝ) else 0)
          (fun _ _ => by positivity) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    positivity

def unusedPrecoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  ∃ ij : Fin b × Fin 4, ∃ d ∈ unusedDirections a, ∃ s : Bool,
    OnLine p (constituent M d s) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))

theorem aligned_unusedPrecoverage_probability_le :
    offsetProbability (fun M => Aligned P a bits p M ∧ unusedPrecoverage P a bits p M) ≤
      offsetProbability (Aligned P a bits p) *
        (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  let E : ((Fin b × Fin 4) × (Direction F × Bool)) → MergedPairs F → Prop :=
    fun z M => Aligned P a bits p M ∧ z.2.1 ∈ unusedDirections a ∧
      OnLine p (constituent M z.2.1 z.2.2) ∧
      OnLine (prescribedPoint P a bits M z.1) (constituent M z.2.1 (!z.2.2))
  have heq : (fun M => Aligned P a bits p M ∧ unusedPrecoverage P a bits p M) =
      (fun M => ∃ z, E z M) := by
    funext M
    apply propext
    constructor
    · rintro ⟨hA, ij, d, hd, s, hp, hx⟩
      exact ⟨(ij, d, s), hA, hd, hp, hx⟩
    · rintro ⟨⟨ij, d, s⟩, hA, hd, hp, hx⟩
      exact ⟨hA, ij, d, hd, s, hp, hx⟩
  rw [heq]
  apply (offsetProbability_exists_le_sum E).trans
  calc
    (∑ z, offsetProbability (E z)) ≤
        ∑ _z : ((Fin b × Fin 4) × (Direction F × Bool)),
          offsetProbability (Aligned P a bits p) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      rintro ⟨ij, d, s⟩ _
      by_cases hd : d ∈ unusedDirections a
      · have heqE : E (ij, d, s) = (fun M => Aligned P a bits p M ∧
            OnLine p (constituent M d s) ∧
            OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))) := by
          funext M
          simp only [E, hd, true_and]
        rw [heqE, aligned_partner_incidence_probability d hd s ij]
      · have hzero : offsetProbability (E (ij, d, s)) = 0 := by
          simp only [offsetProbability, E, hd, false_and, and_false, ite_false,
            Finset.sum_const_zero, zero_div]
        rw [hzero]
        exact mul_nonneg (offsetProbability_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_option, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [inv_pow, ← one_div]
      ring

theorem conditioned_unusedPrecoverage_probability_le :
    conditionedOffsetProbability (Aligned P a bits p) (unusedPrecoverage P a bits p) ≤
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  unfold conditionedOffsetProbability
  by_cases hzero : offsetProbability (Aligned P a bits p) = 0
  · rw [hzero, div_zero]
    positivity
  · have hpos := lt_of_le_of_ne (offsetProbability_nonneg (Aligned P a bits p))
      (Ne.symm hzero)
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ offsetProbability (Aligned P a bits p) *
          (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 :=
        aligned_unusedPrecoverage_probability_le
      _ = _ := by ring

end
end Balanced.Local.UnusedOffsetProbability

end OAI
