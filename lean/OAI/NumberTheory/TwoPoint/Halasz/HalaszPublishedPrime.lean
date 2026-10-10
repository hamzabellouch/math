import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSparseGram
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The precise published prime-supported sparse estimate needed for the
extra-prime argument. `HalaszPrimeSparseInput` specializes Matomäki--Radziwiłł,
*Multiplicative functions in short intervals*, Annals 183 (2016), Lemma 11
(arXiv:1501.04585v4), to T=exp L and epsilon=1/12. Replacing log Y by log p
costs at most an absolute factor on [Y,2Y]. -/
namespace TwoPointCorrelations

open Filter Finset

def HalaszPrimeSparseInput : Prop :=
  ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
    ∀ (a : ℕ → ℂ) (S : Finset ℝ),
    (∀ t ∈ S, |t| ≤ Real.exp L) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      C*(Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2)*
        ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)

lemma halasz_sparse_prime_error :
    ∀ᶠ L : ℝ in atTop, ∀ Y R : ℝ,
      L^(79/80:ℝ) ≤ Real.log Y → 0 ≤ R → R ≤ Real.exp (L^(3/100:ℝ)) →
      R*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 ≤ 1 := by
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<19/80 by norm_num)).bound
    (show (0:ℝ)<1/4 by norm_num)
  have hpow := (tendsto_rpow_atTop (show (0:ℝ)<83/400 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hlog,hpow,eventually_ge_atTop (1:ℝ)] with L hlog hpow hL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have hprod : L^(3/100:ℝ)*L^(83/400:ℝ)=L^(19/80:ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hsmall : 2*L^(3/100:ℝ) ≤ L^(19/80:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hL0.le (3/100))
    rw [hprod] at hh
    linarith
  intro Y R hY _hR hRbound
  have hquot : L^(79/80:ℝ)/L^(3/4:ℝ)=L^(19/80:ℝ) := by
    rw [← Real.rpow_sub hL0]
    norm_num
  have hlarge : L^(19/80:ℝ) ≤ Real.log Y/L^(3/4:ℝ) := by
    rw [← hquot]
    exact div_le_div_of_nonneg_right hY (Real.rpow_nonneg hL0.le _)
  have hsq : L^2=Real.exp (2*Real.log L) := by
    rw [show 2*Real.log L=Real.log L+Real.log L by ring,Real.exp_add,Real.exp_log hL0]
    ring
  calc
    _ ≤ Real.exp (L^(3/100:ℝ))*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 := by
      gcongr
    _ = Real.exp (L^(3/100:ℝ)-Real.log Y/L^(3/4:ℝ)+2*Real.log L) := by
      rw [hsq,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem HalaszPrimeSparseInput.short_prime_energy (hprime : HalaszPrimeSparseInput) :
    ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ∀ H Y : ℝ, B ≤ H → 2 ≤ Y → H^2 ≤ Y →
      L^(79/80:ℝ) ≤ Real.log Y → 1 ≤ Real.log Y →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      (∀ p ∈ P, Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H) →
      OneBounded F → ∀ (S : Finset ℝ),
      (∀ t ∈ S, |t| ≤ Real.exp L) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ) ≤ Real.exp (L^(3/100:ℝ)) →
      (∑ t ∈ S, ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖^2) ≤ C/(H*(Real.log Y)^2) := by
  obtain ⟨C₁,L₀,hC₁,hprime⟩ := hprime
  obtain ⟨C₂,B,hC₂,hB,hmass⟩ := mrt_short_prime_logarithmic_mass
  refine ⟨2*C₁*C₂,B,by positivity,hB,?_⟩
  filter_upwards [halasz_sparse_prime_error,eventually_ge_atTop L₀,
    eventually_ge_atTop (1:ℝ)] with L herror hL₀ hL
  intro H Y hH hY hHY hYL hlogY P F hP hwindow hF S hheight hsep hcard
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hlogY0 : 0 < Real.log Y := by linarith
  have he := herror Y S.card hYL (Nat.cast_nonneg _) hcard
  have hkernel := hprime L Y hL₀ hL hY P hP (fun p => F p/(p:ℂ)) S hheight hsep
  have hpref : Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 ≤ 2*Y := by
    have hh := mul_le_mul_of_nonneg_left he hY0.le
    nlinarith
  have hm := hmass H (Real.log Y) P F hH hlogY
    (by simpa only [Real.exp_log hY0] using hHY)
    (fun p hp => ⟨(hP p hp).1,(hwindow p hp).1,(hwindow p hp).2⟩) hF
  rw [Real.exp_log hY0] at hm
  calc
    _ ≤ C₁*(2*Y)*(∑ p ∈ P, ‖F p/(p:ℂ)‖^2/Real.log (p:ℝ)) :=
      hkernel.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpref hC₁.le)
        (sum_nonneg (fun p hp => div_nonneg (sq_nonneg _)
          (by have hh := (hwindow p hp).1; linarith))))
    _ ≤ C₁*(2*Y)*(C₂/(H*Y*(Real.log Y)^2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp [hH0.ne',hY0.ne',hlogY0.ne']

end TwoPointCorrelations

end OAI
