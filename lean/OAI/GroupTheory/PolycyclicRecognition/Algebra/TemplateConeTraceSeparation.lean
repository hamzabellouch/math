import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateConeTraces

namespace OAI

/-! # The actual transformed pure-word traces determine the offset -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Apply the forward and reversed volume tests to the same transformed
ray quotient and to each independent two-ray quotient. The positive
pure-word multiplicities then force equality of the original offsets. -/
theorem eq_of_transformed_pure_word_trace_inequalities
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (cRay : I → ℕ) (cTwo : I → I → ℕ)
    (houtRay : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → cRay i = 0)
    (hinRay : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → 0 < cRay i)
    (houtTwo : ∀ k (h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]),
      ∀ i, (D.weight i).toContinuousLinearMap ∉
        transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
          (D.weight k).toContinuousLinearMap h) A.val → cTwo k i = 0)
    (hinTwo : ∀ k (h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]),
      ∀ i, (D.weight i).toContinuousLinearMap ∈
        transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
          (D.weight k).toContinuousLinearMap h) A.val → 0 < cTwo k i)
    (x y : W)
    (hray : (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (hray' : (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0)
    (htwo : ∀ k, LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap] →
      (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (htwo' : ∀ k, LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap] →
      (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0) :
    x = y := by
  classical
  let w := A.val.symm (y - x)
  have hzero (ell : W →L[ℝ] ℝ) (hp : ell (y - x) ≤ 0) (hn : ell (x - y) ≤ 0) :
      ell (y - x) = 0 := by
    rw [map_sub] at hp hn ⊢
    linarith
  obtain ⟨r, hr, he⟩ := transformed_ray_trace_pos_multiple D A hne j cRay houtRay hinRay
  have hα : (D.weight j) w = 0 := by
    have hv := congrArg (fun f : W →L[ℝ] ℝ => f w) he
    have hz := hzero _ hray hray'
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      smul_eq_mul] at hv
    change (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (A.val w) =
      r * (D.weight j) w at hv
    have hw : A.val w = y - x := A.val.apply_symm_apply _
    rw [hw, hz] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left hr.ne'
  have hw : w = 0 := D.separates w (by
    intro k
    by_cases hind : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]
    · obtain ⟨u, v, _, hvpos, he⟩ := transformed_two_ray_trace_pos_coefficients D A
        hne j k hind (cTwo k) (houtTwo k hind) (hinTwo k hind)
      have hv := congrArg (fun f : W →L[ℝ] ℝ => f w) he
      have hz := hzero _ (htwo k hind) (htwo' k hind)
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        smul_apply, smul_eq_mul] at hv
      change (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (A.val w) =
        u * (D.weight j) w + v * (D.weight k) w at hv
      have hw : A.val w = y - x := A.val.apply_symm_apply _
      rw [hw, hz] at hv
      change 0 = u * (D.weight j) w + v * (D.weight k) w at hv
      rw [hα, mul_zero, zero_add] at hv
      exact (mul_eq_zero.mp hv.symm).resolve_left hvpos.ne'
    · have hαne : (D.weight j).toContinuousLinearMap ≠ 0 := by simpa using hne j
      obtain ⟨c, hc⟩ : ∃ c : ℝ,
          c • (D.weight j).toContinuousLinearMap = (D.weight k).toContinuousLinearMap := by
        simpa only [LinearIndependent.pair_iff' hαne, not_forall, not_not] using hind
      have hh := congrArg (fun f : W →L[ℝ] ℝ => f w) hc
      change c * (D.weight j) w = (D.weight k) w at hh
      rw [hα, mul_zero] at hh
      exact hh.symm)
  have he := congrArg A.val hw
  have hz : y - x = 0 := by simpa [w] using he
  exact (sub_eq_zero.mp hz).symm

end PolycyclicRecognition

end

end OAI
