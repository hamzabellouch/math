import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInterpolationBound

namespace OAI

/-! # An elementary one-variable Remez bound

The constant is deliberately coarse. Only a fixed power of inverse length is
needed in the subexponential geometric argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial

theorem univariate_remez_bound (D : ℕ) (hD : 1 ≤ D) (p : ℝ[X])
    (hp : p.natDegree ≤ D) (R : ℝ) (hR : 1 ≤ R)
    (S : Set ℝ) (hS : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal)
    (η : ℝ) (hη : 0 ≤ η) (hvalues : ∀ x ∈ S, |p.eval x| ≤ η)
    (x : ℝ) (hx : x ∈ closedBall 0 R) :
    |p.eval x| ≤
      (8 * ((D + 1 : ℕ) : ℝ) ^ 2 * (1 + R) / (volume S).toReal) ^ D * η := by
  classical
  let N : ℝ := (D + 1 : ℕ)
  let m := (volume S).toReal
  let δ := m / (4 * N)
  have hN : 1 ≤ N := by dsimp [N]; norm_cast; omega
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hlength : 2 * N * δ < m := by
    dsimp [δ]
    field_simp
    nlinarith
  obtain ⟨s, hs, hsS, hsep⟩ :=
    exists_separated_finset_of_length S δ hδ (D + 1) hlength
  have hdegree : p.degree < s.card := by
    rw [hs]
    exact (natDegree_le_iff_degree_le.mp hp).trans_lt (by exact_mod_cast Nat.lt_succ_self D)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb := polynomial_bound_of_separated_nodes p s hdegree δ R η hδ hR0 hη hsep
    (fun a ha => by simpa [mem_closedBall, Real.dist_eq] using hS (hsS ha))
    (fun a ha => hvalues a (hsS ha)) x
    (by simpa [mem_closedBall, Real.dist_eq] using hx)
  rw [hs, Nat.add_sub_cancel] at hb
  change |p.eval x| ≤ N * η * (2 * R / δ) ^ D at hb
  have hNpow : N ≤ N ^ D := by
    calc
      N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ D := pow_le_pow_right₀ hN hD
  have hbase : N * (2 * R / δ) ≤ 8 * N ^ 2 * (1 + R) / m := by
    have heq : N * (2 * R / δ) = 8 * N ^ 2 * R / m := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg N]) hm.le
  calc
    |p.eval x| ≤ N * η * (2 * R / δ) ^ D := hb
    _ ≤ N ^ D * η * (2 * R / δ) ^ D := by gcongr
    _ = (N * (2 * R / δ)) ^ D * η := by rw [mul_pow]; ring
    _ ≤ (8 * N ^ 2 * (1 + R) / m) ^ D * η := by
      apply mul_le_mul_of_nonneg_right _ hη
      exact pow_le_pow_left₀ (by positivity) hbase D

/-- The scalar interval sublevel estimate. -/
theorem exists_univariate_remez_constant (D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : ℝ[X]), p.natDegree ≤ D → ∀ R : ℝ, 1 ≤ R →
      ∀ S : Set ℝ, S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |p.eval x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |p.eval x| ≤ (A * (1 + R) / (volume S).toReal) ^ D * η := by
  refine ⟨8 * ((D + 1 : ℕ) : ℝ) ^ 2, by positivity, ?_⟩
  exact fun p hp R hR S hS hm η hη hv x hx =>
    univariate_remez_bound D hD p hp R hR S hS hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
