import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyEnvelope
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSum

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem adaptive_sqrt_two_pow (n : ℕ) : Real.sqrt ((2:ℝ)^n) = Real.sqrt 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]

def adaptiveSmallSupport (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 (L^4)).filter (fun s => Squarefree s ∧ s.Coprime L)

theorem adaptive_small_scale {L d s v : ℕ} (hL : 0 < L) (hd : 0 < d)
    (hs : 0 < s) (hv : 0 < v) (hsL : s ≤ L^4) (hdL : d ≤ L) (hvL : v ≤ L)
    {R : ℝ} (hR : (L^6:ℕ) ≤ R) :
    (d:ℝ) ≤ Real.sqrt (R/((s:ℝ)*v/d)) := by
  have hdr : (0:ℝ)<d := by exact_mod_cast hd
  have hsr : (0:ℝ)<s := by exact_mod_cast hs
  have hvr : (0:ℝ)<v := by exact_mod_cast hv
  have hR0 : 0 < R := (by exact_mod_cast pow_pos hL 6 : (0:ℝ)<(L^6:ℕ)).trans_le hR
  apply (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).mpr
  apply (le_div_iff₀ (by positivity : 0<(s:ℝ)*v/d)).mpr
  calc
    _ = (s:ℝ)*v*d := by field_simp
    _ ≤ (L:ℝ)^4*L*L := by gcongr; exact_mod_cast ‹_›
    _ = (L^6:ℕ) := by push_cast; ring
    _ ≤ R := hR

theorem divisorQuadraticSumP_small_norm_le {L d s v : ℕ} (hL : Squarefree L)
    (hd : d ∈ L.divisors) (hv : v ∈ L.divisors) (hs : 0 < s) (hsL : s ≤ L^4)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (P : ℕ)
    {R : ℝ} (hR : (L^6:ℕ) ≤ R) (h θ : ℝ) :
    ‖divisorQuadraticSumP d A mInv s v P R h θ‖ ≤
      2*cutoffFourierBound*Real.sqrt ((2:ℝ)^d.primeFactors.card) := by
  let : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  let : NeZero (∏ p : d.primeFactors,p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have hdsq := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hscale := adaptive_small_scale hL.ne_zero.bot_lt (Nat.pos_of_mem_divisors hd) hs
    (Nat.pos_of_mem_divisors hv) hsL
    (Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd))
    (Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hv)) hR
  have he := centeredQuadraticSum_small_norm_le (fun p : d.primeFactors => p.val)
    (divisor_coordinate_prime d) (divisor_coordinates_coprime d) (fun p => A p.val)
    (mInv:ZMod (∏ p : d.primeFactors,p.val)) s v P R h θ
    (by simpa only [divisor_coordinates_product hdsq] using hscale)
  simpa only [divisorQuadraticSumP,Fintype.card_coe] using he

def adaptiveSmallEnvelope (L : ℕ) (lam B : ℝ) : ℝ :=
  B*(1+Real.sqrt 2*lam)^L.primeFactors.card*reciprocalSqrtDivisorSum L

theorem adaptiveSmallEnvelope_nonneg (L : ℕ) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    0 ≤ adaptiveSmallEnvelope L lam B := by
  unfold adaptiveSmallEnvelope
  exact mul_nonneg (mul_nonneg hB (pow_nonneg (by positivity) _)) (reciprocalSqrtDivisorSum_nonneg L)

theorem positiveDivisorArray_small_envelope {L s : ℕ} (hL : Squarefree L)
    (q : ℕ) {lam B : ℝ} (hlam : 0 ≤ lam) (_hB : 0 ≤ B)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (hs : 0 < s)
    (P : ℕ) (R h θ : ℝ)
    (hG : ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ B*Real.sqrt ((2:ℝ)^d.primeFactors.card)) :
    ‖positiveDivisorArray L q lam A mInv P R h θ s‖ ≤
      adaptiveSmallEnvelope L lam B/Real.sqrt (s:ℝ) := by
  have hinner (v : ℕ) (hv : v ∈ L.divisors) :
      ‖∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*
        divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤
        B*(1+Real.sqrt 2*lam)^L.primeFactors.card := by
    calc
      _ ≤ ∑ d ∈ L.divisors,‖(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*
          divisorQuadraticSumP d A (mInv d) s v P R h θ‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ L.divisors,B*(Real.sqrt 2*lam)^d.primeFactors.card := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlam]
        calc
          _ ≤ (lam^d.primeFactors.card*1)*(B*Real.sqrt ((2:ℝ)^d.primeFactors.card)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (adaptive_jacobi_norm_le d q) (pow_nonneg hlam _))
              (hG d hd v hv) (norm_nonneg _) (by positivity)
          _ = _ := by rw [adaptive_sqrt_two_pow,mul_pow]; ring
      _ = _ := by rw [←Finset.mul_sum,positive_array_divisor_weight_sum hL]
  have houter : ‖∑ v ∈ L.divisors,(jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ)*
      ∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*
        divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ adaptiveSmallEnvelope L lam B := by
    calc
      _ ≤ ∑ v ∈ L.divisors,‖(jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ)*
          ∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*
            divisorQuadraticSumP d A (mInv d) s v P R h θ‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ L.divisors,(Real.sqrt (v:ℝ))⁻¹*(B*(1+Real.sqrt 2*lam)^L.primeFactors.card) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        apply mul_le_mul _ (hinner v hv) (norm_nonneg _) (by positivity)
        simpa only [one_div] using div_le_div_of_nonneg_right (adaptive_jacobi_norm_le v q) (Real.sqrt_nonneg (v:ℝ))
      _ = _ := by rw [←Finset.sum_mul]; unfold adaptiveSmallEnvelope reciprocalSqrtDivisorSum; ring
  unfold positiveDivisorArray
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq (by ring)

end Ostmann.QuadraticCenter

end

end OAI
