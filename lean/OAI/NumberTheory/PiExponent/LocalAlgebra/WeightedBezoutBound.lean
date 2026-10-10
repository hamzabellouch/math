import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalBezout
import OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPowerLength
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight
import OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights

namespace OAI

open scoped BigOperators
namespace PiExponent.WeightedBezout

noncomputable def pointLength {k : Type*} [Field k] {n : ℕ}
    (a : Fin n → k) (I : Ideal (MvPolynomial (Fin n) k)) : ℕ∞ :=
  Module.length (Localization.AtPrime (pointIdeal a))
    (Localization.AtPrime (pointIdeal a) ⧸ I.map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (pointIdeal a))))

theorem pointLength_translatedPowerSubstitution {k : Type*} [Field k] {n : ℕ}
    (a : Fin n → k) (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    pointLength (0 : Fin n → k) (I.map (translatedPowerSubstitution w a).toRingHom) =
      pointLength a I * ((∏ i, w i : ℕ) : ℕ∞) :=
  RamifiedLocalLength.translatedPowerLocal_quotient_length w a hw I

theorem finite_length_of_rank_bound {L : ℕ∞} {r B : ℕ}
    (hr : 0 < r) (h : L * (r : ℕ∞) ≤ (B : ℕ∞)) :
    ∃ l : ℕ, L = (l : ℕ∞) ∧ l * r ≤ B := by
  have hfin : L ≠ ⊤ := by
    intro ht
    have hr0 : (r : ℕ∞) ≠ 0 := by exact_mod_cast hr.ne'
    rw [ht, ENat.top_mul hr0] at h
    exact (ENat.natCast_ne_top B) (top_le_iff.mp h)
  refine ⟨L.toNat, (ENat.natCast_toNat hfin).symm, ?_⟩
  have hn : ((L.toNat * r : ℕ) : ℕ∞) ≤ B := by
    simpa only [Nat.cast_mul, ENat.natCast_toNat hfin] using h
  exact_mod_cast hn

theorem weighted_bound_of_scaled_natural {n M L B : ℕ}
    (ρ : Fin n → ℝ) (w : Fin n → ℕ) (N : ℝ)
    (hM : 0 < M) (hρ : ∀ i, 0 < ρ i)
    (hw : ∀ i, (w i : ℝ) = (M : ℝ) * ρ i)
    (hbound : L * ∏ i, w i ≤ B ^ n)
    (hdegree : (B : ℝ) ≤ (M : ℝ) * N) :
    (L : ℝ) ≤ N ^ n / ∏ i, ρ i := by
  have hp : 0 < ∏ i, ρ i := Finset.prod_pos (fun i _ => hρ i)
  have hscale : 0 < (M : ℝ) ^ n := pow_pos (by exact_mod_cast hM) _
  have hprod : (∏ i, (w i : ℝ)) = (M : ℝ) ^ n * ∏ i, ρ i := by
    simp_rw [hw]
    rw [Finset.prod_mul_distrib]
    simp
  apply (le_div_iff₀ hp).mpr
  apply (mul_le_mul_iff_right₀ hscale).mp
  calc
    (M : ℝ) ^ n * ((L : ℝ) * ∏ i, ρ i) = (L : ℝ) * ∏ i, (w i : ℝ) := by
      rw [hprod]
      ring
    _ ≤ (B : ℝ) ^ n := by exact_mod_cast hbound
    _ ≤ ((M : ℝ) * N) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg B) hdegree n
    _ = (M : ℝ) ^ n * N ^ n := by rw [mul_pow]

theorem weight_product_comparison {n : ℕ} (ρ κ : Fin n → ℝ) (ε N L : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hκ : ∀ i, 0 < κ i) (hε : 0 < ε) (hN : 0 < N)
    (hlower : (ε * N) ^ n / ((n.factorial : ℝ) * ∏ i, κ i) ≤ L)
    (hupper : L ≤ N ^ n / ∏ i, ρ i) :
    (∏ i, ρ i) ≤ (n.factorial : ℝ) * (∏ i, κ i) / ε ^ n := by
  have hA : 0 < ∏ i, ρ i := Finset.prod_pos (fun i _ => hρ i)
  have hB : 0 < (n.factorial : ℝ) * ∏ i, κ i :=
    mul_pos (by exact_mod_cast Nat.factorial_pos n) (Finset.prod_pos (fun i _ => hκ i))
  have h := (div_le_div_iff₀ hB hA).mp (hlower.trans hupper)
  rw [mul_pow] at h
  apply (le_div_iff₀ (pow_pos hε n)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hN n)).mp
  calc
    N ^ n * ((∏ i, ρ i) * ε ^ n) = ε ^ n * N ^ n * ∏ i, ρ i := by ring
    _ ≤ N ^ n * ((n.factorial : ℝ) * ∏ i, κ i) := h

theorem pointLength_mul_le_of_substituted_degree
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (D : ℕ)
    (hdegree : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    pointLength a (Ideal.span (Set.range f)) * (∏ i, w i : ℕ) ≤ (D ^ n : ℕ) := by
  let I := Ideal.span (Set.range f)
  let g : J → MvPolynomial (Fin n) k := fun j => translatedPowerSubstitution w a (f j)
  have hmap : I.map (translatedPowerSubstitution w a).toRingHom =
      Ideal.span (Set.range g) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hminimal0 := origin_minimalPrimes_map w a hw I hminimal
  rw [hmap] at hminimal0
  have hheight := PiExponentSiegelAux.W09.polynomialMaximal_height k n
    (pointIdeal (0 : Fin n → k))
  have hb := PiExponent.localIsolatedBezout k n g D n hdegree
    (pointIdeal (0 : Fin n → k)) hminimal0 hheight le_rfl
  rw [← hmap] at hb
  rw [RamifiedLocalLength.translatedPowerLocal_quotient_length w a hw I] at hb
  exact hb

theorem pointLength_mul_le
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (D : ℕ)
    (hdegree : ∀ j, (f j).weightedTotalDegree w ≤ D)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    pointLength a (Ideal.span (Set.range f)) * (∏ i, w i : ℕ) ≤ (D ^ n : ℕ) :=
  pointLength_mul_le_of_substituted_degree k f a w hw D
    (fun j => (translatedPowerSubstitution_totalDegree w a (f j)).trans (hdegree j))
    hminimal

theorem rational_pointLength_bound
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (ρ : Fin n → ℚ) (hρ : ∀ i, 0 < ρ i) (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ N)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    ∃ L : ℕ, pointLength a (Ideal.span (Set.range f)) = (L : ℕ∞) ∧
      (L : ℝ) ≤ N ^ n / ∏ i, (ρ i : ℝ) := by
  classical
  obtain ⟨M, hM, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hscale : ∀ i, (w i : ℝ) = (M : ℝ) * (ρ i : ℝ) := by
    intro i
    rw [hweights i]
    field_simp
  have hMN : 0 ≤ (M : ℝ) * N := mul_nonneg hMreal.le hN
  let D : ℕ := ⌊(M : ℝ) * N⌋₊
  have hD : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D := by
    intro j
    apply (Nat.le_floor_iff hMN).mpr
    exact translatedPowerSubstitution_totalDegree_real w a
      (fun i => (ρ i : ℝ)) M N hMreal.le hMN hscale (f j) (hdegree j)
  have hbound := pointLength_mul_le_of_substituted_degree k f a w hw D hD hminimal
  have hprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  obtain ⟨L, hL, hLbound⟩ := finite_length_of_rank_bound hprod hbound
  refine ⟨L, hL, ?_⟩
  exact weighted_bound_of_scaled_natural (fun i => (ρ i : ℝ)) w N hM
    (fun i => by exact_mod_cast hρ i) hscale hLbound (Nat.floor_le hMN)

end PiExponent.WeightedBezout

end OAI
