import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeTrace

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The ray with its vertex omitted. Generator weights are nonzero. -/
def positiveWeightRay (α : V) : Set V := {β | ∃ c : ℝ, 0 < c ∧ β = c • α}

/-- The pointed two-generator cone with its vertex omitted. -/
def positiveWeightCone (α η : V) : Set V :=
  {β | ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ 0 < c + d ∧ β = c • α + d • η}

theorem positiveWeightRay_add (α : V) :
    ∀ x ∈ positiveWeightRay α, ∀ y ∈ positiveWeightRay α, x + y ∈ positiveWeightRay α := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩
  exact ⟨c + d, add_pos hc hd, (add_smul c d α).symm⟩

theorem zero_not_mem_positiveWeightRay {α : V} (hα : α ≠ 0) :
    (0 : V) ∉ positiveWeightRay α := by
  rintro ⟨c, hc, he⟩
  exact (smul_ne_zero (ne_of_gt hc) hα) he.symm

theorem positiveWeightCone_add (α η : V) :
    ∀ x ∈ positiveWeightCone α η, ∀ y ∈ positiveWeightCone α η,
      x + y ∈ positiveWeightCone α η := by
  rintro x ⟨a, b, ha, hb, hab, rfl⟩ y ⟨c, d, hc, hd, hcd, rfl⟩
  refine ⟨a + c, b + d, add_nonneg ha hc, add_nonneg hb hd, by linarith, ?_⟩
  simp only [add_smul]
  abel

theorem zero_not_mem_positiveWeightCone {α η : V} (h : LinearIndependent ℝ ![α, η]) :
    (0 : V) ∉ positiveWeightCone α η := by
  rintro ⟨c, d, _, _, hcd, he⟩
  have hh := h.eq_of_pair (s := c) (t := d) (s' := 0) (t' := 0) (by simpa using he.symm)
  simp only [hh.1, hh.2, add_zero, lt_self_iff_false] at hcd

theorem positiveWeightRay_self (α : V) : α ∈ positiveWeightRay α :=
  ⟨1, zero_lt_one, (one_smul ℝ α).symm⟩

theorem positiveWeightCone_left (α η : V) : α ∈ positiveWeightCone α η := by
  exact ⟨1, 0, zero_le_one, le_rfl, by norm_num, by simp⟩

theorem positiveWeightCone_right (α η : V) : η ∈ positiveWeightCone α η := by
  exact ⟨0, 1, le_rfl, zero_le_one, by norm_num, by simp⟩

/-- Positive integral multiplicities on a ray give a positive ray character. -/
theorem positive_sum_on_weightRay {I : Type*} [Fintype I]
    (α : V) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightRay α → c i = 0)
    (i₀ : I) (h₀ : β i₀ ∈ positiveWeightRay α) (hc₀ : 0 < c i₀) :
    ∃ a : ℝ, 0 < a ∧ ∑ i, (c i : ℝ) • β i = a • α := by
  classical
  have hd (i) : ∃ d : ℝ, 0 ≤ d ∧
      (c i : ℝ) • β i = ((c i : ℝ) * d) • α ∧
      (β i ∈ positiveWeightRay α → 0 < d) := by
    by_cases hi : β i ∈ positiveWeightRay α
    · obtain ⟨d, hd, he⟩ := hi
      exact ⟨d, hd.le, by rw [he, smul_smul], fun _ => hd⟩
    · exact ⟨0, le_rfl, by simp [hout i hi], fun h => False.elim (hi h)⟩
  choose d hd he hp using hd
  refine ⟨∑ i, (c i : ℝ) * d i, ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hc₀) (hp i₀ h₀))
      (Finset.single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hd i))
        (Finset.mem_univ i₀))
  · simp_rw [he]
    rw [Finset.sum_smul]

/-- A two-generator cone character has a positive coefficient on each
extreme ray when both corresponding generators occur. -/
theorem positive_sum_on_weightCone {I : Type*} [Fintype I]
    (α η : V) (hind : LinearIndependent ℝ ![α, η]) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightCone α η → c i = 0)
    (i₀ i₁ : I) (h₀ : β i₀ = α) (h₁ : β i₁ = η) (hc₀ : 0 < c i₀) (hc₁ : 0 < c i₁) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∑ i, (c i : ℝ) • β i = a • α + b • η := by
  classical
  have hd (i) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      (c i : ℝ) • β i = ((c i : ℝ) * a) • α + ((c i : ℝ) * b) • η ∧
      (β i ∈ positiveWeightCone α η → β i = a • α + b • η) := by
    by_cases hi : β i ∈ positiveWeightCone α η
    · obtain ⟨a, b, ha, hb, _, he⟩ := hi
      exact ⟨a, b, ha, hb, by rw [he, smul_add, smul_smul, smul_smul], fun _ => he⟩
    · exact ⟨0, 0, le_rfl, le_rfl, by simp [hout i hi], fun h => False.elim (hi h)⟩
  choose a b ha hb he hp using hd
  have hA : a i₀ = 1 := (hind.eq_of_pair (s := a i₀) (t := b i₀) (s' := 1) (t' := 0)
    (by simpa [h₀] using (hp i₀ (h₀ ▸ positiveWeightCone_left α η)).symm)).1
  have hB : b i₁ = 1 := (hind.eq_of_pair (s := a i₁) (t := b i₁) (s' := 0) (t' := 1)
    (by simpa [h₁] using (hp i₁ (h₁ ▸ positiveWeightCone_right α η)).symm)).2
  refine ⟨∑ i, (c i : ℝ) * a i, ∑ i, (c i : ℝ) * b i, ?_, ?_, ?_⟩
  · have hpos : 0 < (c i₀ : ℝ) * a i₀ := by simpa [hA] using (Nat.cast_pos.mpr hc₀ : (0 : ℝ) < c i₀)
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (ha i)) (Finset.mem_univ i₀))
  · have hpos : 0 < (c i₁ : ℝ) * b i₁ := by simpa [hB] using (Nat.cast_pos.mpr hc₁ : (0 : ℝ) < c i₁)
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hb i)) (Finset.mem_univ i₁))
  · simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]

end PolycyclicRecognition

end

end OAI
