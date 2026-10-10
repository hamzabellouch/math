import Mathlib

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

universe u v

variable {K : Type u} [CommSemiring K] {σ : Type v}

/-- A homogeneous polynomial of formal degree zero is a scalar, including
the zero polynomial. -/
theorem homogeneous_zero_eq_C {p : MvPolynomial σ K}
    (hp : p.IsHomogeneous 0) : p = C (constantCoeff p) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr hp

/-- Remove formal-degree-zero factors from a homogeneous product and absorb
them into a single scalar. Positive-degree occurrences, including repeated
occurrences and zero polynomials, are retained. -/
theorem homogeneous_product_positive_factors
    (l : List (MvPolynomial σ K × ℕ))
    (hl : ∀ q ∈ l, q.1.IsHomogeneous q.2) :
    ∃ a : K, ∃ factors : List (MvPolynomial σ K × ℕ),
      (∀ q ∈ factors, 0 < q.2 ∧ q.1.IsHomogeneous q.2) ∧
      (factors.map Prod.snd).sum = (l.map Prod.snd).sum ∧
      (l.map Prod.fst).prod = C a * (factors.map Prod.fst).prod ∧
      factors.Sublist l ∧
      factors.length ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil =>
      exact ⟨1, [], by simp⟩
  | cons q l ih =>
      have hq := hl q (by simp)
      have ht : ∀ r ∈ l, r.1.IsHomogeneous r.2 := by
        intro r hr
        exact hl r (by simp [hr])
      obtain ⟨a, factors, hf, hd, hv, hs, hn⟩ := ih ht
      by_cases hzero : q.2 = 0
      · have hscalar : q.1 = C (constantCoeff q.1) :=
          homogeneous_zero_eq_C (hzero ▸ hq)
        refine ⟨constantCoeff q.1 * a, factors, hf, ?_, ?_, hs.cons q, ?_⟩
        · simpa [hzero] using hd
        · simp only [List.map_cons, List.prod_cons, hv, map_mul]
          conv_lhs => lhs; rw [hscalar]
          simp only [mul_assoc]
        · simpa [hzero] using hn
      · have hpos : 0 < q.2 := Nat.pos_of_ne_zero hzero
        refine ⟨a, q :: factors, ?_, ?_, ?_, hs.cons_cons q, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact ⟨hpos, hq⟩
          · exact hf r hr
        · simpa using congrArg (q.2 + ·) hd
        · simp only [List.map_cons, List.prod_cons, hv]
          ac_rfl
        · simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega

/-- When the original formal degrees are at most one, removing the scalar
factors leaves exactly the total formal degree many homogeneous linear
forms. No assumption on variable support is required. -/
theorem homogeneous_product_linear_factors
    (l : List (MvPolynomial σ K × ℕ))
    (hl : ∀ q ∈ l, q.1.IsHomogeneous q.2)
    (hle : ∀ q ∈ l, q.2 ≤ 1) :
    ∃ a : K, ∃ factors : List (MvPolynomial σ K),
      factors.length = (l.map Prod.snd).sum ∧
      (∀ p ∈ factors, p.IsHomogeneous 1) ∧
      (l.map Prod.fst).prod = C a * factors.prod := by
  obtain ⟨a, factors, hf, hd, hv, hs, _⟩ :=
    homogeneous_product_positive_factors l hl
  have hone : ∀ q ∈ factors, q.2 = 1 := by
    intro q hq
    have hpos := (hf q hq).1
    have hbound := hle q (hs.subset hq)
    omega
  have hsum : (factors.map Prod.snd).sum = factors.length := by
    have heq : factors.map Prod.snd = factors.map (fun _ => 1) := by
      apply List.map_eq_map_iff.mpr
      exact hone
    rw [heq]
    simp
  refine ⟨a, factors.map Prod.fst, ?_, ?_, hv⟩
  · simpa only [List.length_map] using hsum.symm.trans hd
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [hone q hq] using (hf q hq).2

end Problem335

end

end OAI
