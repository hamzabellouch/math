import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseRows
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeWindows
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace OAI

/-! The prime-supported sparse mean square keeps the reciprocal logarithmic
weight of the coefficient norm. The Mangoldt kernel estimate is an explicit
local hypothesis; its analytic proof is separate from this finite duality. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

/-- The full reciprocal weight in finite weighted Gram duality. -/
theorem mrt_sparse_divided_weight_energy {ι : Type*}
    (K P : Finset ι) (hPK : P ⊆ K) (w freq : ι → ℝ) (a : ι → ℂ)
    (hw : ∀ n ∈ K, 0 ≤ w n) (hwP : ∀ n ∈ P, 0 < w n)
    (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ P, ‖a n‖^2/w n := by
  let b := fun n => if n ∈ P then a n/(w n:ℂ) else 0
  have hb (n : ι) (hn : n ∈ P) : (w n:ℂ)*b n = a n := by
    have hnz : (w n:ℂ) ≠ 0 := by exact_mod_cast (hwP n hn).ne'
    dsimp only [b]
    rw [ite_eq_left hn]
    field_simp
  have he (t : ℝ) : mrtExponentialPolynomial K (fun n => (w n:ℂ)*b n) freq t =
      mrtExponentialPolynomial P a freq t := by
    unfold mrtExponentialPolynomial
    calc
      _ = ∑ n ∈ P, (w n:ℂ)*b n*Complex.exp (((freq n*t:ℝ):ℂ)*I) := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := sum_congr rfl (fun n hn => by rw [hb n hn])
  have hmass : (∑ n ∈ K, w n*‖b n‖^2) = ∑ n ∈ P, ‖a n‖^2/w n := by
    calc
      _ = ∑ n ∈ P, w n*‖b n‖^2 := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        dsimp only [b]
        rw [ite_eq_left hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hwP n hn)]
        field_simp
  have h := mrt_sparse_weighted_row_energy K w freq b hw S hsep hA hD hkernel
  simpa only [he, hmass] using h

/-- A nonnegative smooth Mangoldt majorant supplies the exact logarithmic
coefficient gain in the prime-supported sparse mean square. -/
theorem mrt_sparse_prime_gram (K P : Finset ℕ) (hPK : P ⊆ K)
    (hP : ∀ p ∈ P, p.Prime) (ψ : ℕ → ℝ)
    (hψ : ∀ n ∈ K, 0 ≤ ψ n) (hψP : ∀ p ∈ P, 1 ≤ ψ p)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K
        (fun n => (ψ n * ArithmeticFunction.vonMangoldt n:ℝ))
        (fun n => -Real.log (n:ℝ)) (t-s)‖ ≤ A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := by
  let w := fun n => ψ n * ArithmeticFunction.vonMangoldt n
  have hlog (p : ℕ) (hp : p ∈ P) : 0 < Real.log (p:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (hP p hp).one_lt
  have hlow (p : ℕ) (hp : p ∈ P) : Real.log (p:ℝ) ≤ w p := by
    dsimp only [w]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hψP p hp) (hlog p hp).le
  have hwP (p : ℕ) (hp : p ∈ P) : 0 < w p := (hlog p hp).trans_le (hlow p hp)
  have hh := mrt_sparse_divided_weight_energy K P hPK w
    (fun n => -Real.log (n:ℝ)) a
    (fun n hn => mul_nonneg (hψ n hn) ArithmeticFunction.vonMangoldt_nonneg)
    hwP S hsep hA hD hkernel
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum (fun p hp =>
    div_le_div_of_nonneg_left (sq_nonneg _) (hlog p hp) (hlow p hp))

/-- The coefficient mass in a short logarithmic prime interval has both
logarithmic savings needed by the prime-supported sparse estimate. -/
theorem mrt_short_prime_logarithmic_mass : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (H u : ℝ) (P : Finset ℕ) (F : ℕ → ℂ), B ≤ H → 1 ≤ u →
      H^2 ≤ Real.exp u →
      (∀ p ∈ P, p.Prime ∧ u ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ u+1/H) →
      OneBounded F →
      (∑ p ∈ P, ‖F p/(p:ℂ)‖^2/Real.log (p:ℝ)) ≤
        C/(H*Real.exp u*u^2) := by
  obtain ⟨C,B,hC,hB,hwindow⟩ := halasz_prime_log_window_bound
  refine ⟨C,B,hC,hB,?_⟩
  intro H u P F hBH hu hscale hP hF
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) (hB.trans hBH)
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hmass := hwindow H u P hBH hu hscale hP
  calc
    _ ≤ ∑ p ∈ P, (1/(Real.exp u*u^2))*(Real.log (p:ℝ)/(p:ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast (hP p hp).1.pos
      have hl : 0 < Real.log (p:ℝ) := hu0.trans_le (hP p hp).2.1
      have hey : Real.exp u ≤ (p:ℝ) := by
        simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr (hP p hp).2.1
      have hn : ‖F p/(p:ℂ)‖ ≤ 1/(p:ℝ) := by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right (hF p (hP p hp).1.pos) hp0.le
      have hd : Real.exp u*u^2 ≤ (p:ℝ)*(Real.log (p:ℝ))^2 := by
        exact mul_le_mul hey (pow_le_pow_left₀ hu0.le (hP p hp).2.1 2)
          (sq_nonneg _) hp0.le
      calc
        _ ≤ (1/(p:ℝ))^2/Real.log (p:ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) hl.le
        _ = (1/((p:ℝ)*(Real.log (p:ℝ))^2))*(Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le (by positivity) hd) (by positivity)
    _ = (1/(Real.exp u*u^2))*∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ (1/(Real.exp u*u^2))*(C/H) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
