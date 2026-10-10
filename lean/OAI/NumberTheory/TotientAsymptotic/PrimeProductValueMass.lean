import OAI.NumberTheory.TotientAsymptotic.FordUnbandedMass
import OAI.NumberTheory.TotientAsymptotic.PrimeExtensionCoverage
import OAI.NumberTheory.TotientAsymptotic.CofactorMass

namespace OAI

/-! Distinct residual values of a prime prefix carry no preimage multiplicity. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def primeProductValues {N : ℕ} (P : Finset (Fin N → ℕ)) (D : Finset ℕ) : Finset ℕ :=
  (P.product D).image (fun z => z.2 * (∏ i, z.1 i).totient)

lemma primeProductValues_positive {N : ℕ} {P : Finset (Fin N → ℕ)} {D : Finset ℕ}
    (hP : ∀ p ∈ P, ∀ i, (p i).Prime) (hD : ∀ d ∈ D, 0 < d) :
    ∀ v ∈ primeProductValues P D, 0 < v := by
  rintro v hv
  obtain ⟨⟨p,d⟩,hpd,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp,hd⟩ := Finset.mem_product.mp hpd
  apply Nat.mul_pos (hD d hd)
  exact Nat.totient_pos.mpr (Finset.prod_pos (fun i _ => (hP p hp i).pos))

lemma primeProductValues_mass {N : ℕ} (P : Finset (Fin N → ℕ)) (D : Finset ℕ)
    (hP : ∀ p ∈ P, ∀ i, (p i).Prime) :
    (∑ v ∈ primeProductValues P D, (v:ℝ)⁻¹) ≤
      (∑ p ∈ P, reciprocalShiftWeight p)*(∑ d ∈ D,(d:ℝ)⁻¹) := by
  unfold primeProductValues
  have hh := Finset.sum_image_le_of_nonneg (s:=P.product D)
    (g:=fun z : (Fin N → ℕ) × ℕ => z.2*(∏ i, z.1 i).totient)
    (f:=fun v : ℕ => (v:ℝ)⁻¹) (fun v _ => inv_nonneg.mpr (Nat.cast_nonneg v))
  apply hh.trans
  calc
    _ = ∑ p ∈ P, ∑ d ∈ D, ((d*(∏ i, p i).totient:ℕ):ℝ)⁻¹ :=
      Finset.sum_product P D (fun z => ((z.2*(∏ i, z.1 i).totient:ℕ):ℝ)⁻¹)
    _ ≤ ∑ p ∈ P, ∑ d ∈ D, reciprocalShiftWeight p*(d:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hnat := totient_prime_product_lower Finset.univ p 1 (fun i _ => hP p hp i)
      simp only [Nat.totient_one,one_mul] at hnat
      have hpos : (0:ℝ) < (∏ i, (p i-1):ℕ) := by
        exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hP p hp i).one_lt)
      have hrec := inv_anti₀ hpos (Nat.cast_le.mpr hnat)
      apply Finset.sum_le_sum
      intro d _
      simp only [Nat.cast_mul,mul_inv_rev]
      exact mul_le_mul_of_nonneg_right hrec (inv_nonneg.mpr (Nat.cast_nonneg d))
    _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul]

/-- Count values with a large leading prime after encoding the remaining
prefix and its cofactor by their distinct totient values. -/
theorem large_prime_product_value_count : ∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ, ∀ P : Finset (Fin N → ℕ), ∀ D Q : Finset ℕ,
      (∀ p ∈ P, ∀ i, (p i).Prime) → (∀ d ∈ D, 0 < d) →
      (∀ v ∈ Q, ∃ n p : ℕ, 0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
        x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ primeProductValues P D) →
      (Q.card:ℝ) ≤ (64*x/Real.log x)*
        (∑ p ∈ P,reciprocalShiftWeight p)*(∑ d ∈ D,(d:ℝ)⁻¹) := by
  filter_upwards [large_prime_totient_count,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro N P D Q hP hD hQ
  have hh := hx (primeProductValues P D) Q (primeProductValues_positive hP hD) hQ
  apply hh.trans
  have hc : 0 ≤ 64*x/Real.log x := by
    exact div_nonneg (by positivity) (Real.log_pos hx1).le
  have hm := mul_le_mul_of_nonneg_left (primeProductValues_mass P D hP) hc
  simpa only [mul_assoc] using hm

end TotientAsymptotic

end

end OAI
