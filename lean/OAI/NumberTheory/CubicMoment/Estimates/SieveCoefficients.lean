import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeJoin
import OAI.NumberTheory.CubicGram.SieveMajorant

namespace OAI

/-!
# Support and divisor bounds for the dispersion sieve coefficients

The coefficients are the actual finite least-common-multiple collection
of the truncated Möbius square, not an abstract majorant hypothesis.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieveCoefficient_nonzero (C : Finset Eisenstein) (e : Eisenstein)
    (he : collectedSquarefreeSieveCoefficient C e ≠ 0) :
    ∃ a ∈ C, ∃ b ∈ C, primarySquarefreeJoin a b = e := by
  have hne : ((C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e)).Nonempty := by
    by_contra h
    apply he
    unfold collectedSquarefreeSieveCoefficient
    apply Finset.sum_eq_zero
    intro t ht
    exact (h ⟨t,ht⟩).elim
  obtain ⟨⟨a,b⟩,hab⟩ := hne
  have h := Finset.mem_filter.mp hab
  exact ⟨a,(Finset.mem_product.mp h.1).1,b,(Finset.mem_product.mp h.1).2,h.2⟩

/-- A pair of divisors of length at most `D` contributes only at a
primary squarefree modulus of norm at most `D²`. -/
theorem collectedSieveCoefficient_support (C : Finset Eisenstein) {D : ℝ} (hD : 0 ≤ D)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c ∧ norm c ≤ D) (e : Eisenstein)
    (he : collectedSquarefreeSieveCoefficient C e ≠ 0) :
    primary e ∧ Squarefree e ∧ norm e ≤ D^2 := by
  obtain ⟨a,ha,b,hb,hjoin⟩ := collectedSieveCoefficient_nonzero C e he
  rw [← hjoin]
  refine ⟨primarySquarefreeJoin_primary (hC a ha).1 (hC b hb).1,
    primarySquarefreeJoin_squarefree (hC a ha).1 (hC b hb).1,?_⟩
  exact (primarySquarefreeJoin_norm_le (hC a ha).1 (hC b hb).1).trans
    (by simpa only [pow_two] using mul_le_mul (hC a ha).2.2 (hC b hb).2.2 (norm_nonneg _) hD)

lemma abs_idealMoebius_real_le_one (a : Eisenstein) : |(idealMoebius a : ℝ)| ≤ 1 := by
  simpa only [Complex.norm_intCast] using norm_idealMoebius_le_one a

/-- The number of possible ordered divisor pairs controls the collected
coefficient. This is the square-divisor bound required for the sieve. -/
theorem collectedSieveCoefficient_abs_le (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (e : Eisenstein) :
    |collectedSquarefreeSieveCoefficient C e| ≤
      ((2 : ℝ)^(primaryPrimeFactors e).card)^2 := by
  by_cases he : collectedSquarefreeSieveCoefficient C e = 0
  · rw [he,abs_zero]
    exact sq_nonneg _
  have hprimary : primary e := by
    obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero C e he
    rw [← hab]
    exact primarySquarefreeJoin_primary (hC a ha).1 (hC b hb).1
  let T := C.filter (· ∣ e)
  let F := (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e)
  have hsub : F ⊆ T.product T := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    have ha := (Finset.mem_product.mp ht'.1).1
    have hb := (Finset.mem_product.mp ht'.1).2
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨ha,ht'.2 ▸ dvd_primarySquarefreeJoin_left (hC t.1 ha).1 (hC t.1 ha).2⟩
    · exact Finset.mem_filter.mpr ⟨hb,ht'.2 ▸ dvd_primarySquarefreeJoin_right (hC t.2 hb).1 (hC t.2 hb).2⟩
  have hT : (T.card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors e).card :=
    primary_divisors_card_le C hC hprimary
  calc
    _ ≤ ∑ t ∈ F, |(idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)| :=
      by simpa only [Real.norm_eq_abs,collectedSquarefreeSieveCoefficient,F,
          Finset.product_eq_sprod] using
        (norm_sum_le (s := F) (f := fun t => (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)))
    _ ≤ ∑ _t ∈ F, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have h := mul_le_mul (abs_idealMoebius_real_le_one t.1)
        (abs_idealMoebius_real_le_one t.2) (abs_nonneg _) (show (0:ℝ) ≤ 1 by norm_num)
      simpa only [mul_one] using h
    _ = (F.card : ℝ) := by simp
    _ ≤ ((T.product T).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (T.card : ℝ)^2 := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_product T T)
      simpa only [Nat.cast_mul,pow_two,Finset.product_eq_sprod] using hh
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hT 2

/-- The divisor loss is an arbitrarily small fixed power, uniformly in
all choices of the truncation set. -/
theorem collectedSieveCoefficient_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C : Finset Eisenstein),
      (∀ c ∈ C, primary c ∧ Squarefree c) → ∀ e : Eisenstein,
      |collectedSquarefreeSieveCoefficient C e| ≤ K*norm e^ε := by
  obtain ⟨K,hK,hbound⟩ := primeDivisorWeight_small_power (ε/2) (by linarith)
  refine ⟨K^2,pow_pos hK _,?_⟩
  intro C hC e
  by_cases he : collectedSquarefreeSieveCoefficient C e = 0
  · rw [he,abs_zero]
    exact mul_nonneg (sq_nonneg K) (Real.rpow_nonneg (norm_nonneg e) ε)
  obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero C e he
  have hep : primary e := hab ▸ primarySquarefreeJoin_primary (hC a ha).1 (hC b hb).1
  have hes : Squarefree e := hab ▸ primarySquarefreeJoin_squarefree (hC a ha).1 (hC b hb).1
  have hh := hbound e hep hes
  apply (collectedSieveCoefficient_abs_le C hC e).trans
  calc
    _ ≤ (K*norm e^(ε/2))^2 := pow_le_pow_left₀ (by positivity) hh 2
    _ = K^2*norm e^ε := by
      rw [mul_pow,← Real.rpow_natCast (norm e^(ε/2)) 2,← Real.rpow_mul (norm_nonneg e)]
      congr 2
      norm_num

end CubicFirstMoment

end

end OAI
