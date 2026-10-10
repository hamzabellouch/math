import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTransformedPolarTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TemplateWeightRays
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IndependentWeightCone

namespace OAI

/-! # Positive trace tests after a template symmetry

The pure-word multiplicities on a transformed cone give a positive test
on each of its original extreme rays. The inverse template symmetry
supplies actual generator weights on those rays.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

theorem positive_sum_on_weightCone_of_scaled_extremes
    {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I]
    (α η : V) (hind : LinearIndependent ℝ ![α, η]) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightCone α η → c i = 0)
    (i₀ i₁ : I) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h₀ : β i₀ = s • α) (h₁ : β i₁ = t • η)
    (hc₀ : 0 < c i₀) (hc₁ : 0 < c i₁) :
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
  have hm₀ : β i₀ ∈ positiveWeightCone α η := by
    exact ⟨s, 0, hs.le, le_rfl, by simpa, by simpa using h₀⟩
  have hm₁ : β i₁ ∈ positiveWeightCone α η := by
    exact ⟨0, t, le_rfl, ht.le, by simpa, by simpa using h₁⟩
  have hA : a i₀ = s := (hind.eq_of_pair (s := a i₀) (t := b i₀) (s' := s) (t' := 0)
    (by simpa [h₀] using (hp i₀ hm₀).symm)).1
  have hB : b i₁ = t := (hind.eq_of_pair (s := a i₁) (t := b i₁) (s' := 0) (t' := t)
    (by simpa [h₁] using (hp i₁ hm₁).symm)).2
  refine ⟨∑ i, (c i : ℝ) * a i, ∑ i, (c i : ℝ) * b i, ?_, ?_, ?_⟩
  · have hpos : 0 < (c i₀ : ℝ) * a i₀ := by
      rw [hA]
      exact mul_pos (Nat.cast_pos.mpr hc₀) hs
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (ha i)) (Finset.mem_univ i₀))
  · have hpos : 0 < (c i₁ : ℝ) * b i₁ := by
      rw [hB]
      exact mul_pos (Nat.cast_pos.mpr hc₁) ht
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hb i)) (Finset.mem_univ i₁))
  · simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B) (A : templateSymmetryGroup D)

/-- Every source generator ray is attained by a target generator after pullback. -/
theorem templateSymmetry_weight_ray_surjective
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (s : ℝ), 0 < s ∧
      (D.weight i).comp A.val.toLinearMap = s • D.weight j := by
  obtain ⟨i, r, hr, he⟩ := templateSymmetry_weight_ray D A⁻¹ j hj
  change (D.weight j).comp A.val.symm.toLinearMap = r • D.weight i at he
  refine ⟨i, r⁻¹, inv_pos.mpr hr, ?_⟩
  ext w
  have hw := LinearMap.congr_fun he (A.val w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply, smul_eq_mul] at hw ⊢
  rw [hw, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

private theorem pulled_weight_ne_zero (hne : ∀ i, D.weight i ≠ 0) (i : I) :
    ((D.weight i).toContinuousLinearMap.comp A.val.toLinearMap.toContinuousLinearMap) ≠ 0 := by
  intro he
  apply hne i
  ext w
  have hw := congrArg (fun f : W →L[ℝ] ℝ => f (A.val.symm w)) he
  simpa using hw

/-- The actual positive multiplicities of the transformed ray quotient
give a positive multiple of the source ray when pulled back. -/
theorem transformed_ray_trace_pos_multiple
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (c : I → ℕ)
    (hout : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → c i = 0)
    (hin : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → 0 < c i) :
    ∃ r : ℝ, 0 < r ∧
      (∑ i, (c i : ℝ) • (D.weight i).toContinuousLinearMap).comp
        A.val.toLinearMap.toContinuousLinearMap = r • (D.weight j).toContinuousLinearMap := by
  let α := (D.weight j).toContinuousLinearMap
  let β := fun i => (D.weight i).toContinuousLinearMap.comp
    A.val.toLinearMap.toContinuousLinearMap
  have hα : α ≠ 0 := by simpa [α] using hne j
  obtain ⟨i, s, hs, hsi⟩ := templateSymmetry_weight_ray_surjective D A j (hne j)
  have hi : β i ∈ positiveWeightRay α := by
    refine ⟨s, hs, ?_⟩
    exact congrArg LinearMap.toContinuousLinearMap hsi
  have hc : 0 < c i := hin i (by
    change β i ∈ (closedWeightRay α hα : Set _)
    rw [closedWeightRay_eq_insert]
    exact mem_insert_of_mem _ hi)
  have hout' : ∀ i, β i ∉ positiveWeightRay α → c i = 0 := by
    intro i h
    apply hout i
    change β i ∉ (closedWeightRay α hα : Set _)
    rw [closedWeightRay_eq_insert]
    rintro (hz | hm)
    · exact pulled_weight_ne_zero D A hne i hz
    · exact h hm
  obtain ⟨r, hr, he⟩ := positive_sum_on_weightRay α β c hout' i hi hc
  refine ⟨r, hr, ?_⟩
  ext w
  simpa [β, α, sum_apply] using
    congrArg (fun f : W →L[ℝ] ℝ => f w) he

/-- For two independent source generators the transformed quotient trace
has a strictly positive coefficient on each source extreme ray. -/
theorem transformed_two_ray_trace_pos_coefficients
    (hne : ∀ i, D.weight i ≠ 0) (j k : I)
    (hind : LinearIndependent ℝ
      ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap])
    (c : I → ℕ)
    (hout : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
        (D.weight k).toContinuousLinearMap hind) A.val → c i = 0)
    (hin : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
        (D.weight k).toContinuousLinearMap hind) A.val → 0 < c i) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      (∑ i, (c i : ℝ) • (D.weight i).toContinuousLinearMap).comp
        A.val.toLinearMap.toContinuousLinearMap =
      r • (D.weight j).toContinuousLinearMap + s • (D.weight k).toContinuousLinearMap := by
  let α := (D.weight j).toContinuousLinearMap
  let η := (D.weight k).toContinuousLinearMap
  let β := fun i => (D.weight i).toContinuousLinearMap.comp
    A.val.toLinearMap.toContinuousLinearMap
  obtain ⟨i₀, r, hr, h₀⟩ := templateSymmetry_weight_ray_surjective D A j (hne j)
  obtain ⟨i₁, s, hs, h₁⟩ := templateSymmetry_weight_ray_surjective D A k (hne k)
  have hβ₀ : β i₀ = r • α := congrArg LinearMap.toContinuousLinearMap h₀
  have hβ₁ : β i₁ = s • η := congrArg LinearMap.toContinuousLinearMap h₁
  have hi₀ : β i₀ ∈ positiveWeightCone α η :=
    ⟨r, 0, hr.le, le_rfl, by simpa, by simpa using hβ₀⟩
  have hi₁ : β i₁ ∈ positiveWeightCone α η :=
    ⟨0, s, le_rfl, hs.le, by simpa, by simpa using hβ₁⟩
  have hc (i : I) (hi : β i ∈ positiveWeightCone α η) : 0 < c i := hin i (by
    change β i ∈ (closedTwoWeightCone α η hind : Set _)
    rw [closedTwoWeightCone_eq_insert]
    exact mem_insert_of_mem _ hi)
  have hout' : ∀ i, β i ∉ positiveWeightCone α η → c i = 0 := by
    intro i h
    apply hout i
    change β i ∉ (closedTwoWeightCone α η hind : Set _)
    rw [closedTwoWeightCone_eq_insert]
    rintro (hz | hm)
    · exact pulled_weight_ne_zero D A hne i hz
    · exact h hm
  obtain ⟨u, v, hu, hv, he⟩ := positive_sum_on_weightCone_of_scaled_extremes α η hind
    β c hout' i₀ i₁ hr hs hβ₀ hβ₁ (hc i₀ hi₀) (hc i₁ hi₁)
  refine ⟨u, v, hu, hv, ?_⟩
  ext w
  simpa [β, α, η, sum_apply] using
    congrArg (fun f : W →L[ℝ] ℝ => f w) he

end PolycyclicRecognition

end

end OAI
