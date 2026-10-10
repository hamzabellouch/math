import OAI.NumberTheory.JointDickman.Counting.FiniteWeightCofactorWindow

namespace OAI

/-! # Uniform finite-weight cofactor cancellation -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

lemma finite_weight_cofactor_logarithmic_overlap : ∃ K : ℕ, 2 ≤ K ∧
    ∀ m : ℕ, K ≤ m → ∀ n : ℕ, m ≤ n → n ≤ 3*m →
      2*(Real.log (n:ℝ))^8 ≤ 3*(Real.log (m:ℝ))^8 := by
  have hh := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (31*Real.log 3))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hh
  refine ⟨max K 2,le_max_right _ _,?_⟩
  intro m hm n hmn hn
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hmr : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnr : 0 < (n:ℝ) := hmr.trans_le (by exact_mod_cast hmn)
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hlm := hK m ((le_max_left _ _).trans hm)
  change 31 * Real.log 3 ≤ Real.log (m:ℝ) at hlm
  have hln : Real.log (n:ℝ) ≤ (32/31:ℝ)*Real.log m := by
    have hs : (n:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast hn
    have hb := Real.log_le_log hnr hs
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hmr.ne'] at hb
    linarith
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hp := pow_le_pow_left₀ hlogn hln 8
  rw [mul_pow] at hp
  have he : 2*(32/31:ℝ)^8 ≤ 3 := by norm_num
  nlinarith [pow_nonneg hlogm 8]

theorem finite_weight_count_window_away_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c →
        p^k ≤ ⌊(2*N:ℝ)/a⌋₊ → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D,p)*n) = f n) →
      ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧
        (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
        ‖mrtCofactorPolynomial P (finiteWeightedCoefficient f E w) N a t‖ ≤ ε := by
  obtain ⟨T,K₁,hT,hK₁,hsmall⟩ := finite_weight_count_window_logarithmic hc hc1 E hE hε
  obtain ⟨K₂,_,hlarge⟩ := high_frequency_count_window hc hc1 E hε
  obtain ⟨K₃,_,hoverlap⟩ := finite_weight_cofactor_logarithmic_overlap
  refine ⟨T,max K₁ (max K₂ K₃),hT,hK₁.trans (le_max_left _ _),?_⟩
  intro N a ha hm f hf hfb hlocal hinv P hP hdis w hw t htlo hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm₁ : K₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : K₂ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm₃ : K₃ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  by_cases ht : |t| ≤ 3*(Real.log (m:ℝ))^8
  · exact hsmall N a ha hm₁ f hf hfb hlocal hinv P hP hdis w hw t htlo ht
  have hm2 : 2 ≤ m := hK₁.trans hm₁
  have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hx : 2 ≤ (N:ℝ)/a := hm2r.trans (Nat.floor_le (by positivity))
  obtain ⟨_,hmn,hnm⟩ := mrt_cofactor_window_ratio N (by linarith : 0 < a) hx
  change m ≤ n at hmn
  change n ≤ 3*m at hnm
  have ho := hoverlap m hm₃ n hmn hnm
  have hlo : 2*(Real.log (n:ℝ))^8 ≤ |t| := ho.trans (le_of_not_ge ht)
  have heq : ∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (n:ℝ)^c → finiteWeightedCoefficient f E w p = 1 := by
    intro p hp hpE hpc
    rw [finiteWeightedCoefficient_prime_outside hE w hp hpE]
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpn : (p:ℝ) ≤ n := hpc.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hc1)
    have hpcast : p ≤ n := by exact_mod_cast hpn
    have hpow : p^1 ≤ ⌊(2*N:ℝ)/a⌋₊ := by
      simpa only [pow_one] using hpcast
    have hh := hlocal p 1 hp (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpc)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpow)
    simpa only [pow_one] using hh
  have hb := hlarge N a ha hm₂ (finiteWeightedCoefficient f E w)
    (finiteWeightedCoefficient_multiplicative f hf hE w)
    (finiteWeightedCoefficient_norm f hfb hw) heq ∅ P (by simp) (fun p hp => (hP p hp).1) t hlo hthi
  have he : mrtMissingCoefficient (finiteWeightedCoefficient f E w) ∅ =
      (finiteWeightedCoefficient f E w : ℕ → ℂ) := by
    funext n
    simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
  rwa [he] at hb

end JointDickman

end OAI
