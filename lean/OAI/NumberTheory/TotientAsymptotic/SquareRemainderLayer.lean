import OAI.NumberTheory.TotientAsymptotic.TwoExceptionalPrimeLayer
import OAI.NumberTheory.TotientAsymptotic.ShiftDivisorMass
import OAI.NumberTheory.TotientAsymptotic.SquareDivisor

namespace OAI

/-! Each single or double shifted-prime divisibility costs a square reciprocal. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareRemainderCase (x : ℝ) (H q j k : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    if j=k then q^2 ∣ remainderPrime η j-1
    else q ∣ remainderPrime η j-1 ∧ q ∣ remainderPrime η k-1)

lemma square_remainder_case_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ i j k q : ℕ, 1 ≤ i → i ≤ R x H → i ≤ j → j ≤ L x H →
      i ≤ k → k ≤ L x H → q.Prime →
      let b := fordBandScale x i
      let A := 1+Real.log (discardPrimeBound b : ℝ)
      (∑ η ∈ squareRemainderCase x H q j k, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (A^2*(D*(2*b+2))^(m x-i))*((q : ℝ)^2)⁻¹ := by
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨D+1,by linarith,?_⟩
  filter_upwards [restricted_prime_layer_mass hbox hren,restricted_two_prime_layer_mass hbox hren,
    ford_band_polynomial_lower 1,eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hone htwo hpoly hH hP
  filter_upwards [hone,htwo,hpoly,basic_suffix_discard_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x h1 h2 hp hbound hBx
  intro i j k q hi hiR hij hjL hik hkL hq
  dsimp only
  let b := fordBandScale x i
  let N := discardPrimeBound b
  let A := 1+Real.log (N : ℝ)
  let E := (D+1)*(2*b+2)
  let C := (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)
  let S := squareRemainderCase x H q j k
  let n := i-1
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb : 2 ≤ b := by
    have hh := hp i him hHi
    simp only [pow_one] at hh
    exact (show (2 : ℝ) ≤ (m x-i : ℕ) by exact_mod_cast hH.trans hHi).trans hh
  have hN : 4 ≤ N := (discardPrimeBound_bounds hb).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA : 1 ≤ A := by dsimp [A]; linarith [Real.log_nonneg hN1]
  have hE : 1 ≤ E := by dsimp [E]; nlinarith
  have hC : 0 ≤ C := mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (G_pos hBx _).le
  have hn : n ≤ R x H := by dsimp [n]; omega
  have hnj : n < j := by dsimp [n]; omega
  have hnk : n < k := by dsimp [n]; omega
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hU : ∀ η ∈ S, ∀ l ∈ Finset.Icc (n+1) (L x H), remainderPrime η l ∈ Nat.primesLE N := by
    intro η hη l hl
    obtain ⟨hl1,hlL⟩ := Finset.mem_Icc.mp hl
    exact hbound H i l (by omega) (by dsimp [n] at hl1; omega) hlL him hb η (hS η hη)
  have hmassU : (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ E := by
    have h := discardPrimeBound_bounds hb
    have hh := (hall N (by omega) h.2.1).trans
      (mul_le_mul_of_nonneg_left (show 1+B (N : ℝ) ≤ 2*b+2 by linarith [h.2.2.1]) hD.le)
    exact hh.trans (by dsimp [E]; nlinarith)
  have hpow (e : ℕ) (he : e ≤ m x-i) :
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)^e ≤ E^(m x-i) :=
    (pow_le_pow_left₀ (by positivity) hmassU e).trans (pow_le_pow_right₀ hE he)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  by_cases hjk : j=k
  · subst k
    have hV : ∀ η ∈ S, remainderPrime η j ∈ shiftDivisiblePrimes N (q^2) := by
      intro η hη
      refine Finset.mem_filter.mpr ⟨hU η hη j (Finset.mem_Icc.mpr ⟨by omega,hjL⟩),?_⟩
      simpa only [S,squareRemainderCase,ite_true] using (Finset.mem_filter.mp hη).2
    have hh := h1 S n j hn hnj hjL _ _ hS hU hV
    have hv := shifted_divisor_mass N (pow_pos hq.pos 2)
    have hv' : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A^2/((q : ℝ)^2) := by
      have ha : A ≤ A^2 := by nlinarith
      have hvA : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/((q : ℝ)^2) := by
        simpa only [A,Nat.cast_pow] using hv
      exact hvA.trans (div_le_div_of_nonneg_right ha (by positivity))
    calc
      _ ≤ C*(A^2/((q : ℝ)^2))*E^(m x-i) := hh.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hv' hC)
        (hpow _ (by dsimp [n]; unfold L; omega)) (by positivity) (by positivity))
      _ = _ := by dsimp [C,E,A,N,b]; ring
  · have hV : ∀ η ∈ S, remainderPrime η j ∈ shiftDivisiblePrimes N q := by
      intro η hη
      refine Finset.mem_filter.mpr ⟨hU η hη j (Finset.mem_Icc.mpr ⟨by omega,hjL⟩),?_⟩
      have hh := (Finset.mem_filter.mp hη).2
      exact (show q ∣ remainderPrime η j-1 ∧ q ∣ remainderPrime η k-1 from by simpa only [S,squareRemainderCase,ite_eq_right hjk] using hh).1
    have hW : ∀ η ∈ S, remainderPrime η k ∈ shiftDivisiblePrimes N q := by
      intro η hη
      refine Finset.mem_filter.mpr ⟨hU η hη k (Finset.mem_Icc.mpr ⟨by omega,hkL⟩),?_⟩
      have hh := (Finset.mem_filter.mp hη).2
      exact (show q ∣ remainderPrime η j-1 ∧ q ∣ remainderPrime η k-1 from by simpa only [S,squareRemainderCase,ite_eq_right hjk] using hh).2
    have hh := h2 S n j k hn hnj hjL hnk hkL hjk _ _ _ hS hU hV hW
    have hv : (∑ p ∈ shiftDivisiblePrimes N q, ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/(q : ℝ) := shifted_divisor_mass N hq.pos
    calc
      _ ≤ C*(A/(q : ℝ))*(A/(q : ℝ))*E^(m x-i) := hh.trans (mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hv hC) hv (by positivity) (by positivity))
        (hpow _ (by dsimp [n]; unfold L; omega)) (by positivity) (by positivity))
      _ = _ := by dsimp [C,E,A,N,b]; ring

end TotientAsymptotic

end

end OAI
