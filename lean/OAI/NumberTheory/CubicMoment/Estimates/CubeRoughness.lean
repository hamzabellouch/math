import OAI.NumberTheory.CubicMoment.Estimates.CubeExclusions

namespace OAI

/-! A finite prime-cover bound for restoring coprimality in the cube term. -/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_tsum_restriction_le_cover (f : Eisenstein → ℂ) (hf : Summable f)
    (P : Finset Eisenstein) (U : Eisenstein → Prop)
    (hcover : ∀ j, U j → ∃ p ∈ P, p ∣ j) :
    ‖∑' j : Eisenstein, if U j then f j else 0‖ ≤
      ∑ p ∈ P, ∑' j : Eisenstein, if p ∣ j then ‖f j‖ else 0 := by
  have hu : Summable (fun j => if U j then f j else 0) := by
    apply hf.norm.of_norm_bounded
    intro j
    split_ifs <;> simp
  have hp (p : Eisenstein) : Summable (fun j => if p ∣ j then ‖f j‖ else 0) := by
    apply hf.norm.of_nonneg_of_le
    · intro j; split_ifs <;> positivity
    · intro j; split_ifs <;> simp
  calc
    _ ≤ ∑' j : Eisenstein, ‖if U j then f j else 0‖ := norm_tsum_le_tsum_norm hu.norm
    _ ≤ ∑' j : Eisenstein, ∑ p ∈ P, if p ∣ j then ‖f j‖ else 0 := by
      apply Summable.tsum_le_tsum _ hu.norm (summable_sum (fun p _ => hp p))
      intro j
      by_cases hj : U j
      · obtain ⟨p,hp,hpj⟩ := hcover j hj
        simp only [ite_eq_left hj]
        exact (by simpa only [ite_eq_left hpj] using
          (Finset.single_le_sum (f := fun r => if r ∣ j then ‖f j‖ else 0)
            (fun r _ => by split_ifs <;> positivity) hp))
      · simp only [ite_eq_right hj,norm_zero]
        exact Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity)
    _ = _ := Summable.tsum_finsetSum (fun p _ => hp p)

/-- Restoring coprimality costs exactly the expected sum of reciprocal
prime norms. The estimate is uniform over the lattice scale. -/
theorem radial_cube_coprimality_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ a b : Eisenstein,
      primary a → Squarefree a → primary b → Squarefree b →
      ‖(∑' j : Eisenstein, if j = 0 then 0 else
          radialDualProfile W (q^3*(norm j)^3)) -
        (∑' j : Eisenstein, if j = 0 then 0 else
          (if IsCoprime a j ∧ IsCoprime b j then
            radialDualProfile W (q^3*(norm j)^3) else 0))‖ ≤
        K/q * ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_multiples_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq a b ha hsa hb hsb
  let f (j : Eisenstein) : ℂ := if j = 0 then 0 else radialDualProfile W (q^3*(norm j)^3)
  let P := primaryPrimeFactors a ∪ primaryPrimeFactors b
  let U (j : Eisenstein) := ¬(IsCoprime a j ∧ IsCoprime b j)
  have hf : Summable f := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    by_cases hj : j = 0 <;> simp [f,hj]
  have hkeep : Summable (fun j => if U j then 0 else f j) := by
    apply hf.norm.of_norm_bounded
    intro j
    split_ifs <;> simp
  have hcover : ∀ j, U j → ∃ p ∈ P, p ∣ j := by
    intro j hj
    rcases not_and_or.mp hj with hj | hj
    · obtain ⟨p,hp,hd⟩ := not_coprime_prime_cover ha hsa hj
      exact ⟨p,Finset.mem_union_left _ hp,hd⟩
    · obtain ⟨p,hp,hd⟩ := not_coprime_prime_cover hb hsb hj
      exact ⟨p,Finset.mem_union_right _ hp,hd⟩
  have hdiff : (∑' j, f j) - (∑' j, if U j then 0 else f j) =
      ∑' j, if U j then f j else 0 := by
    rw [← hf.tsum_sub hkeep]
    apply tsum_congr
    intro j
    split_ifs <;> simp
  have hkeepEq (j : Eisenstein) : (if U j then 0 else f j) =
      if j = 0 then 0 else (if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (q^3*(norm j)^3) else 0) := by
    by_cases hj : j = 0 <;> by_cases hc : IsCoprime a j ∧ IsCoprime b j <;> simp [U,f,hj,hc]
  change ‖(∑' j, f j) - _‖ ≤ _
  simp_rw [← hkeepEq]
  rw [hdiff]
  calc
    _ ≤ ∑ p ∈ P, ∑' j : Eisenstein, if p ∣ j then ‖f j‖ else 0 := by
      convert norm_tsum_restriction_le_cover f hf P U hcover using 2
      apply tsum_congr
      intro j
      by_cases hj : U j <;> simp [hj]
    _ ≤ ∑ p ∈ P, K/(q*norm p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p ≠ 0 := by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact (primaryPrimeFactor_spec ha hp).1.2.ne_zero
        · exact (primaryPrimeFactor_spec hb hp).1.2.ne_zero
      convert hbound q hq p hp0 using 1
      apply tsum_congr
      intro j
      by_cases hpj : p ∣ j <;> by_cases hj : j = 0 <;> simp [f,hpj,hj]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end CubicFirstMoment

end

end OAI
