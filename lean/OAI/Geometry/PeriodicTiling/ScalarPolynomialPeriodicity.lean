import OAI.Geometry.PeriodicTiling.FiniteDifferencePolynomial
import OAI.Geometry.PeriodicTiling.PolynomialWeyl
import OAI.Geometry.PeriodicTiling.RationalPolynomialPeriod

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set Polynomial
open scoped Topology

theorem denseRange_circlePolynomial_of_irrational_coefficient (P : Polynomial ℝ)
    (hP : ∃ i : ℕ, 0 < i ∧ Irrational (P.coeff i)) :
    DenseRange (fun n : ℤ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) := by
  obtain ⟨a, ha, Q, hQ, hI, hvalues⟩ := exists_progression_irrational_leadingCoeff P hP
  have hd := denseRange_circlePolynomial_of_irrational_leadingCoeff Q hQ hI
  apply Dense.mono (s₁ := Set.range (fun n : ℕ => ((Q.eval (n : ℝ) : ℝ) : UnitAddCircle))) _ hd
  rintro _ ⟨n, rfl⟩
  refine ⟨((a * n : ℕ) : ℤ), ?_⟩
  simpa only [Int.cast_natCast] using hvalues n

theorem circle_polynomial_periodic_of_not_dense (f : ℤ → UnitAddCircle)
    (r : ℕ) (hpoly : (forwardDiff^[r]) f = 0) (hnd : ¬ DenseRange f) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  obtain ⟨P, hP⟩ := exists_polynomial_lift_of_iter_forwardDiff_eq_zero f r hpoly
  have hrat : ∀ i : ℕ, 0 < i → ∃ q : ℚ, P.coeff i = (q : ℝ) := by
    intro i hi
    by_contra h
    have hirr : Irrational (P.coeff i) := by
      rintro ⟨q, hq⟩
      exact h ⟨q, hq.symm⟩
    apply hnd
    have hd := denseRange_circlePolynomial_of_irrational_coefficient P ⟨i, hi, hirr⟩
    have heq : (fun n : ℤ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) = f := funext hP
    rwa [heq] at hd
  obtain ⟨q, hq, hper⟩ := rational_nonconstant_circlePolynomial_periodic P hrat
  refine ⟨q, hq, ?_⟩
  intro n
  rw [← hP (n + q), ← hP n]
  exact hper n

theorem circle_polynomial_periodic_of_omits_open (f : ℤ → UnitAddCircle)
    (r : ℕ) (hpoly : (forwardDiff^[r]) f = 0)
    (U : Set UnitAddCircle) (hU : IsOpen U) (hne : U.Nonempty)
    (hmiss : ∀ n, f n ∉ U) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  apply circle_polynomial_periodic_of_not_dense f r hpoly
  intro hd
  obtain ⟨n, hn⟩ := hd.exists_mem_open hU hne
  exact hmiss n hn

private theorem not_denseRange_circle_of_bounded_lt_one (f : ℤ → ℝ) (c : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (hc : ∀ n, f n ≤ c) (hc1 : c < 1) :
    ¬ DenseRange (fun n => (f n : UnitAddCircle)) := by
  intro hd
  have hc0 : 0 ≤ c := (h0 0).trans (hc 0)
  let K : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Set.Icc 0 c
  have hK : IsClosed K :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hsub : Set.range (fun n => (f n : UnitAddCircle)) ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact ⟨f n, ⟨h0 n, hc n⟩, rfl⟩
  have hm : (((c + 1) / 2 : ℝ) : UnitAddCircle) ∈ K :=
    (closure_minimal hsub hK) (hd _)
  obtain ⟨y, hy, heq⟩ := hm
  have hyI : y ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hy.1, by linarith [hy.2]⟩
  have hmI : (c + 1) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor <;> linarith
  have hyEq : y = (c + 1) / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hmI).mp heq
  rw [hyEq] at hy
  linarith [hy.2]

theorem real_polynomial_periodic_of_bounded_lt_one
    (r : ℕ) (_hr : 0 < r) (f : ℤ → ℝ) (c : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (hc : ∀ n, f n ≤ c) (hc1 : c < 1)
    (hpoly : (forwardDiff^[r]) (fun n => (f n : AddCircle (1 : ℝ))) = 0) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  obtain ⟨q, hq, hper⟩ := circle_polynomial_periodic_of_not_dense
    (fun n => (f n : UnitAddCircle)) r hpoly
    (not_denseRange_circle_of_bounded_lt_one f c h0 hc hc1)
  refine ⟨q, hq, ?_⟩
  intro n
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show f (n + q) ∈ Set.Ico (0 : ℝ) (0 + 1) from
      ⟨h0 _, by simpa using (hc _).trans_lt hc1⟩)
    (show f n ∈ Set.Ico (0 : ℝ) (0 + 1) from
      ⟨h0 _, by simpa using (hc _).trans_lt hc1⟩)).mp
  exact hper n

end PeriodicTilingThree

end

end OAI
