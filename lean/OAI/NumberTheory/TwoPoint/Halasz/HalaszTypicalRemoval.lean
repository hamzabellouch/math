import OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTKernelTail
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFiniteWindows

namespace OAI

/-! Removing the atypical integers from literal short windows costs only
their dyadic density in mean square. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

lemma halasz_short_sum_sub (F G : ℕ → ℂ) (H : ℕ) (α x : ℝ) :
    shortExponentialSum (fun n => F n - G n) H α x =
      shortExponentialSum F H α x - shortExponentialSum G H α x := by
  simp only [shortExponentialSum, sub_mul, sum_sub_distrib]

theorem halasz_exceptional_kernel {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) (hTN : T ≤ N) :
    (∫ t : ℝ, mrtShortKernel T t *
      ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      224 * Real.exp 1 *
        (((Finset.Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N := by
  let b := fun n => F n - mrtTypicalCoefficient J P F n
  let δ := (((Finset.Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N
  let A := 16 * Real.exp 1 * δ
  let C := (∑ n ∈ Finset.Ioc N (2*N), ‖b n‖ * Real.exp (-Real.log (n:ℝ)))^2
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he (t : ℝ) : mrtLogDirichlet (Finset.Ioc N (2*N)) b t =
      mrtDyadicPolynomial F N t - mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t := by
    rw [mrt_log_dirichlet_polynomial _ (fun n hn => hN.trans (Finset.mem_Ioc.mp hn).1)]
    exact halasz_dyadic_sub F (mrtTypicalCoefficient J P F) N t
  have hFc : Continuous (fun t =>
      ‖mrtDyadicPolynomial F N t - mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖^2) :=
    ((mrtExponentialPolynomial_continuous _ _ _).sub
      (mrtExponentialPolynomial_continuous _ _ _)).norm.pow 2
  have hbound (t : ℝ) :
      ‖mrtDyadicPolynomial F N t - mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖^2 ≤ C := by
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm _ _ t) 2
  have hp (v : ℝ) (hv : 0 < v) :
      (∫ t in -v..v, ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖^2) ≤ A*(v/N+1) := by
    have hh := halasz_exceptional_dyadic_energy J P F hF hN hv
    have hr : 0 ≤ v/(N:ℝ) := div_nonneg hv.le hNr.le
    rw [show 8 * Real.exp 1 * (v / N + 2) *
      (((Finset.Ioc N (2*N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N =
        (8 * Real.exp 1 * δ) * (v / N + 2) by dsimp [δ]; ring] at hh
    have hcoef : 0 ≤ 8 * Real.exp 1 * δ := by positivity
    apply hh.trans
    dsimp [A]
    nlinarith [mul_nonneg hcoef hr]
  have hh := mrt_short_kernel_finite_height _ hFc (fun _ => sq_nonneg _) hbound
    hNr hT hTN hA hA (fun v hv _ => hp v (hT.trans_le hv))
    (fun v hv => hp v (hNr.trans_le hv))
  have hratio : (T/(N:ℝ))^2 ≤ 1 := by
    have hle := (div_le_one hNr).mpr hTN
    have hge : 0 ≤ T/(N:ℝ) := div_nonneg hT.le hNr.le
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4*A by positivity)
  apply hh.trans
  calc
    _ ≤ 10*A + 4*A := add_le_add le_rfl (by simpa only [mul_one] using hm)
    _ = _ := by dsimp [A, δ]; ring

theorem halasz_typical_short_error {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N H : ℕ} (hH : 0 < H) (hHN : H ≤ N)
    {δ : ℝ} (hδ : ∀ k ∈ ({N, 2*N} : Finset ℕ),
      (((Finset.Ioc k (2*k)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / k ≤ δ) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H 0 x -
      shortExponentialSum (mrtTypicalCoefficient J P F) H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤ (139968/(2*Real.pi)) * (448*Real.exp 1*δ) := by
  have hN : 0 < N := hH.trans_le hHN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hH1 : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hTN : (N:ℝ)/H ≤ N := (div_le_iff₀ hHr).mpr (by nlinarith)
  have hk (k : ℕ) (hk : k ∈ ({N, 2*N} : Finset ℕ)) :
      (∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t *
        ‖mrtDyadicPolynomial F k t -
          mrtDyadicPolynomial (mrtTypicalCoefficient J P F) k t‖^2) ≤
        224*Real.exp 1*δ := by
    have hNk : N ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    have hh := halasz_exceptional_kernel J P F hF (hN.trans_le hNk)
      (div_pos hNr hHr) (hTN.trans (by exact_mod_cast hNk))
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left (hδ k hk)
      (by positivity : 0 ≤ 224*Real.exp 1)
    simpa only [mul_div_assoc] using hm
  have hh := mrt_literal_short_energy_dyadic
    (fun n => F n - mrtTypicalCoefficient J P F n) hH hHN
  simp_rw [halasz_short_sum_sub, halasz_dyadic_sub] at hh
  have hs := add_le_add (hk N (by simp)) (hk (2*N) (by simp))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

end TwoPointCorrelations

end OAI
