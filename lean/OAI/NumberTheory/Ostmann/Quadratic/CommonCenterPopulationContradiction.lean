import OAI.NumberTheory.Ostmann.Construction.BiasedAffineContradiction
import OAI.NumberTheory.Ostmann.Construction.FiniteBiasPopulation

namespace OAI

/-! # Two biased endpoint populations cannot share a rational center -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_center_divisor_budget (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ L J : ℝ, L ≤ 2 * T ^ 2 →
      Real.exp (3 * T / 5) ≤ J → 4 * L ≤ (c / 4) * J * T := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 3 / 5 by norm_num)).const_mul_left
    (32 / c)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT L J hL hJ
  have heq : Real.exp ((3 / 5 : ℝ) * T) = Real.exp (3 * T / 5) := by congr 1; ring
  rw [heq] at hpoly
  have habs : |(32 / c) * T| ≤ Real.exp (3 * T / 5) := by
    simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _), one_mul,
      mul_div_assoc] using hpoly
  have hpoly' : 32 * T / c ≤ Real.exp (3 * T / 5) := by
    calc
      _ = (32 / c) * T := by ring
      _ ≤ |(32 / c) * T| := le_abs_self _
      _ ≤ _ := habs
  have hh : 32 * T ≤ c * J := by
    have hq := (div_le_iff₀ hc).mp (hpoly'.trans hJ)
    simpa only [mul_comm] using hq
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ T by linarith)
  nlinarith

theorem common_center_biased_populations_impossible (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
        (h : ℤ) (ε δ : ℕ → ℝ) (t : ℕ → ℤ) (S U : Finset ℤ),
        T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
        2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
        0 < J → Real.exp T ≤ Cpop * T * J →
        J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
        Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
        1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
        ∀ hP : ∀ p ∈ P, p.Prime,
        (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
        (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
        (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → (∀ p ∈ P, m < p) →
        (∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) →
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) → (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
        (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) →
        (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ x ∈ U, orientedQuadraticValue δ t x p) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := biased_affine_populations_impossible P₀ H hSiegel
    sieve Cpop hCpop C hM (a * c / 2) (c / 2) (by positivity) (by positivity)
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [hno, eventual_center_divisor_budget c hc] with T hnoT hbudget
  intro L J P k Z M m h ε δ t S U hTL hLU hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL
    hP hodd hPZ hε hδ hlogp hmp ht hm hmU hred hboundS hboundU hmeanS hmeanU
    hspanS hspanU hcross hsizeS hsizeU
  have hcard : 0 < P.card := by exact_mod_cast (Real.exp_pos _).trans_le hsize
  obtain ⟨S', hSS, hScard, hSbias⟩ := commonCenter_biased_population P hP S ε t m h c hc.le
    hm hcard hε hmp ht hmeanS
  obtain ⟨U', hUU, hUcard, hUbias⟩ := commonCenter_biased_population P hP U δ t m h c hc.le
    hm hcard hδ hmp ht hmeanU
  have hSsize : (a * c / 2) * Real.exp (L / 2) / L ^ 6 ≤ S'.card := by
    have hh := mul_le_mul_of_nonneg_right hsizeS (show 0 ≤ c / 2 by positivity)
    calc
      _ = (a * Real.exp (L / 2) / L ^ 6) * (c / 2) := by ring
      _ ≤ (S.card : ℝ) * (c / 2) := hh
      _ = (S.card : ℝ) * c / 2 := by ring
      _ ≤ _ := hScard
  have hUsize : (a * c / 2) * Real.exp (L / 2) / L ^ 6 ≤ U'.card := by
    have hh := mul_le_mul_of_nonneg_right hsizeU (show 0 ≤ c / 2 by positivity)
    calc
      _ = (a * Real.exp (L / 2) / L ^ 6) * (c / 2) := by ring
      _ ≤ (U.card : ℝ) * (c / 2) := hh
      _ = (U.card : ℝ) * c / 2 := by ring
      _ ≤ _ := hUcard
  apply hnoT L J P k Z M m h (commonCenterOrientation ε m) (commonCenterOrientation δ m)
    S' U' hTL hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL hP hodd hPZ
    (fun p hp => commonCenterOrientation_norm ε m p (hε p hp))
    (fun p hp => commonCenterOrientation_norm δ m p (hδ p hp)) hlogp
    (by convert hbudget L P.card hLU hsize using 1; ring)
    hm hmU hred (fun x hx => hboundS x (hSS hx)) (fun x hx => hboundU x (hUU hx))
    hSbias hUbias (fun x hx y hy => hspanS x (hSS hx) y (hSS hy))
    (fun x hx y hy => hspanU x (hUU hx) y (hUU hy))
    (fun x hx y hy => hcross x (hSS hx) y (hUU hy)) hSsize hUsize

end Ostmann

end OAI
