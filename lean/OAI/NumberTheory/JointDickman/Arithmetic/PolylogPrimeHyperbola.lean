import OAI.NumberTheory.JointDickman.Amplification.PolylogHyperbolaBudget

namespace OAI

/-! # A logarithmic-scale bound for the full rational prime sum -/
namespace JointDickman
open Finset

lemma sqrt_polylog_hyperbola_budget (C N B : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    Real.sqrt (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q) ≤
      8*Real.sqrt C/B^3 := by
  have hB0 : 0 < B := by linarith
  have h := mul_le_mul_of_nonneg_left
    (rational_hyperbola_polylog_budget N B q hN hB hq hlog hqlo hqhi) hC
  have he : (8*Real.sqrt C/B^3)^2 = C*(64/B^6) := by
    have hs := Real.sq_sqrt hC
    field_simp
    nlinarith
  calc
    _ ≤ Real.sqrt ((8*Real.sqrt C/B^3)^2) := Real.sqrt_le_sqrt (by simpa [he] using h)
    _ = _ := Real.sqrt_sq (by positivity)

lemma polylog_hyperbola_factor_bound (C N B : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    (1+Real.log N/Real.log 2)*
      (Real.log 4*(2/B^2+2/B^20) + B^2*Real.sqrt
        (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q)) ≤
      (1+3/Real.log 2)*(4*Real.log 4+8*Real.sqrt C) := by
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hBsquare : B ≤ B^2 := le_self_pow₀ hB1 (by norm_num : 2 ≠ 0)
  have hBtwenty : B ≤ B^20 := le_self_pow₀ hB1 (by norm_num : 20 ≠ 0)
  have hround : Real.log 4*(2/B^2+2/B^20) ≤ 4*Real.log 4/B := by
    calc
      _ ≤ Real.log 4*(2/B+2/B) := by gcongr
      _ = _ := by ring
  have hsqrt := sqrt_polylog_hyperbola_budget C N B q hC hN hB hq hlog hqlo hqhi
  have hcore : Real.log 4*(2/B^2+2/B^20) + B^2*Real.sqrt
      (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q) ≤
      (4*Real.log 4+8*Real.sqrt C)/B := by
    calc
      _ ≤ 4*Real.log 4/B + B^2*(8*Real.sqrt C/B^3) :=
        add_le_add hround (mul_le_mul_of_nonneg_left hsqrt (sq_nonneg B))
      _ = _ := by field_simp
  have hprefix : 1+Real.log N/Real.log 2 ≤ (1+3/Real.log 2)*B := by
    have hh := div_le_div_of_nonneg_right hlog hlog2.le
    calc
      _ ≤ 1+3*B/Real.log 2 := add_le_add le_rfl hh
      _ ≤ B+3*B/Real.log 2 := add_le_add hB1 le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1+3/Real.log 2)*B)*((4*Real.log 4+8*Real.sqrt C)/B) := by
      apply mul_le_mul hprefix hcore
      · positivity
      · positivity
    _ = _ := by field_simp

theorem polylog_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N B q a : ℕ), 2 ≤ B → B^20 ≤ N →
    0 < q → a.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
      b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ C*N*(1+Real.log B) := by
  obtain ⟨C,hC,hbound⟩ := full_prime_hyperbola_bound
  let D := (1+3/Real.log 2)*(4*Real.log 4+8*Real.sqrt C)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨40*Real.log 4+D,by positivity,?_⟩
  intro b c N B q a hB hBN hq ha hlog hqlo hqhi hb hc
  have hB0 : 0 < B := by omega
  have hBR : (2:ℝ) ≤ B := by exact_mod_cast hB
  have hNR : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (pow_pos hB0 20) hBN)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have h := hbound b c N (B^20) (B^2) q a
    (by exact_mod_cast hNR) (pow_pos hB0 20) hBN (pow_pos hB0 2) hq ha hb hc
  have hf := polylog_hyperbola_factor_bound C N B q hC.le hNR hBR hq hlog hqlo hqhi
  have hf' : (1+Real.log N/Real.log 2)*(N:ℝ)*
      (Real.log 4*(2/(B:ℝ)^2+2/(B:ℝ)^20) + (B:ℝ)^2*Real.sqrt
        (C*rationalHyperbolaBudget N ((B:ℝ)^20) (Real.log (2*(N:ℝ))) q)) ≤ N*D := by
    dsimp [D]
    convert mul_le_mul_of_nonneg_left hf hNR.le using 1; ring
  have hsmall : 2*(N:ℝ)*Real.log 4*(1+Real.log ((B:ℝ)^20)) ≤
      40*Real.log 4*N*(1+Real.log B) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hNR.le (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))]
  push_cast at h
  have hh := h.trans (add_le_add hsmall hf')
  have hDlog : (N:ℝ)*D ≤ D*N*(1+Real.log B) := by
    nlinarith [mul_nonneg (mul_nonneg hNR.le hD.le) hlogB]
  nlinarith

end JointDickman

end OAI
