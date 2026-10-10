import OAI.NumberTheory.CubicMoment.Decomposition.Decomposition
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetector
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedPrimeWeight (ψ : ℝ → ℝ) (w z : ℝ) (p : Eisenstein) : ℂ :=
  (ψ (norm p/w)-ψ (norm p/z):ℝ)

def primaryFactorRemainder (n : Eisenstein) (s : Finset Eisenstein) : Eisenstein :=
  ∏ p ∈ primaryPrimeFactors n \ s, p

lemma primaryFactorRemainder_spec {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    primary (primaryFactorRemainder n s) ∧ Squarefree (primaryFactorRemainder n s) ∧
      (∏ p ∈ s, p)*primaryFactorRemainder n s = n := by
  have hp : ∀ p ∈ primaryPrimeFactors n \ s, primaryPrime p :=
    fun p h => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp h).1).1
  refine ⟨primary_finset_prod _ _ (fun p h => (hp p h).1),
    primaryPrime_product_squarefree _ hp,?_⟩
  rw [primaryFactorRemainder,mul_comm,Finset.prod_sdiff hsub,primaryPrimeFactors_prod hn hs]

lemma roughProduct_primaryFactorRemainder {n : Eisenstein} (hn : primary n)
    (s : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ) :
    roughProduct ψ w (primaryFactorRemainder n s) =
      ∏ p ∈ primaryPrimeFactors n \ s, (1-ψ (norm p/w)) := by
  rw [roughProduct_primary_factors,primaryFactorRemainder,
    primaryPrimeFactors_finset_prod _ (fun p hp =>
      (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1)]

lemma ordered_subset_product (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ((s.card.factorial:ℂ)⁻¹)*
      (∑ e : Fin s.card ≃ s, ∏ i : Fin s.card, v (e i)) = ∏ p ∈ s, v p := by
  have he : Fin s.card ≃ s :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card s = s.card)).symm
  have hcard : Fintype.card (Fin s.card ≃ s) = s.card.factorial := by
    simpa using Fintype.card_equiv he
  have hprod (e : Fin s.card ≃ s) : (∏ i : Fin s.card, v (e i)) = ∏ p ∈ s, v p := by
    exact (e.prod_comp (fun p : s => v p)).trans (Finset.prod_coe_sort s v)
  simp_rw [hprod]
  rw [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,←mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero s.card)),one_mul]

/-- The exact distinguished expansion with ordered distinct primary
prime tuples and the manuscript's factor `1/i!`. -/
theorem roughProduct_ordered_primary_tuples {n : Eisenstein} (hn : primary n)
    (ψ : ℝ → ℝ) (w z : ℝ) :
    (roughProduct ψ z n:ℂ) =
      ∑ s ∈ (primaryPrimeFactors n).powerset,
        ((s.card.factorial:ℂ)⁻¹)*
          (∑ e : Fin s.card ≃ s,
            (∏ i : Fin s.card, distinguishedPrimeWeight ψ w z (e i)))*
          (roughProduct ψ w (primaryFactorRemainder n s):ℂ) := by
  simp_rw [ordered_subset_product]
  rw [roughProduct_primary_factors]
  push_cast
  rw [distinguished_factor_expansion (primaryPrimeFactors n)
    (fun p => (ψ (norm p/w):ℂ)) (fun p => (ψ (norm p/z):ℂ))]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [roughProduct_primaryFactorRemainder hn]
  simp only [distinguishedPrimeWeight,Complex.ofReal_sub,Complex.ofReal_prod,Complex.ofReal_one]

lemma distinguishedPrimeWeight_support {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein}
    (hp : 0 < norm p) (hne : distinguishedPrimeWeight ψ w z p ≠ 0) :
    w < norm p ∧ norm p < 2*z := by
  have hz : 0 < z := hw.trans_le hwz
  constructor
  · by_contra h
    have hpw : norm p ≤ w := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψone _ (div_pos hp hw) ((div_le_one hw).mpr hpw),
      hψone _ (div_pos hp hz) ((div_le_one hz).mpr (hpw.trans hwz)),sub_self]
    rfl
  · by_contra h
    have hpz : 2*z ≤ norm p := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψzero _ ((le_div_iff₀ hw).mpr (by linarith)),
      hψzero _ ((le_div_iff₀ hz).mpr hpz),sub_self]
    rfl

/-- Every chosen prime is large; the product bound therefore bounds the
number of chosen factors, uniformly in the original squarefree element. -/
lemma primary_factor_subset_card_lt {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {w : ℝ} (hw : 1 ≤ w) (hlarge : ∀ p ∈ s, w ≤ norm p)
    {k : ℕ} (hsize : norm n < w^k) : s.card < k := by
  have hprod : w^s.card ≤ norm n := by
    calc
      _ = ∏ _p ∈ s, w := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod₀ (fun _ _ => zero_le_one.trans hw) hlarge
      _ ≤ (∏ p ∈ s, norm p)*(∏ p ∈ primaryPrimeFactors n \ s, norm p) :=
        le_mul_of_one_le_right (Finset.prod_nonneg (fun p _ => norm_nonneg p))
          (Finset.one_le_prod₀ (fun p hp => one_le_norm
            (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1.2.ne_zero))
      _ = ∏ p ∈ primaryPrimeFactors n, norm p := by
        rw [mul_comm,Finset.prod_sdiff hsub]
      _ = norm n := by
        simpa only [Nat.cast_prod,normNat_cast] using
          congrArg (fun m : ℕ => (m:ℝ)) (primaryPrimeFactors_norm_prod hn hs)
  by_contra h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hw (not_lt.mp h)).trans hprod)) hsize

end CubicFirstMoment

end

end OAI
