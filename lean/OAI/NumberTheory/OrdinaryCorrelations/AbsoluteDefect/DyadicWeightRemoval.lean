import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpSmoothingNumeric
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpWeightTermError
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpWindowZeroHigh

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open OrdinaryGaussianWindow OrdinarySharpWindow Finset Filter MeasureTheory

lemma dyadic_weight_removal {f : ℕ→ℂ} {d : ℕ} (χ : DirichletCharacter ℂ d)
    {X : ℕ} (hX : 0 < X) {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun x : ℝ=>Real.exp (-x)*
      ‖sharpWindow (Ioc X (2*X)) (characterModulation f χ) (fun n=>Real.log n) H x‖) ∧
    (∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc X (2*X))
      (characterModulation f χ) (fun n=>Real.log n) H x‖) ≤
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) H x‖)+
      H^2*(∑n∈Ioc X (2*X),‖characterModulation f χ n/(n:ℂ)‖) := by
  have he : sharpWindow (Ioc X (2*X))
      (fun n=>(characterModulation f χ n/(n:ℂ))*(Real.exp (Real.log n):ℂ))
      (fun n=>Real.log n) H =
      sharpWindow (Ioc X (2*X)) (characterModulation f χ) (fun n=>Real.log n) H := by
    ext x
    apply sum_congr rfl
    intro n hn
    have hnp : 0 < n := hX.trans (mem_Ioc.mp hn).1
    have hnr : (0:ℝ) < n := by exact_mod_cast hnp
    dsimp only
    rw [Real.exp_log hnr,Complex.ofReal_natCast,div_mul_cancel₀ _ (by exact_mod_cast hnp.ne')]
  have hh := sharp_weight_removal (Ioc X (2*X))
    (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) hH
  simpa only [he] using hh

lemma dyadic_weighted_sharp_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      Integrable (fun x : ℝ=>Real.exp (-x)*‖sharpWindow (Ioc X (2*X))
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖) ∧
      (∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc X (2*X))
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖) < ε*(D/(X:ℝ)) := by
  obtain ⟨D0,hD0,hL⟩ := dyadic_sharp_log_window_small hf hm hNP hd χ (by positivity : 0 < ε/2)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0 : (0:ℝ) < D0).trans_le hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt (2*D/ε)
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hX0X hXp
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hH : 0 < D/(X:ℝ) := div_pos hDp hXr
  have hsmall : D/(X:ℝ) < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp (hX0.trans_le (show (X0:ℝ) ≤ (X:ℝ) by exact_mod_cast hX0X))
    apply (div_lt_iff₀ hXr).2
    linarith only [hh]
  obtain ⟨hi,hbound⟩ := dyadic_weight_removal χ (show 0 < X by omega) hH.le (f:=f)
  have hcoeff := mul_le_mul_of_nonneg_left
    (dyadic_coefficient_sum hf χ (show 0 < X by omega)) (sq_nonneg (D/(X:ℝ)))
  refine ⟨hi,?_⟩
  have hh := mul_lt_mul_of_pos_right hsmall hH
  nlinarith only [hbound,hLX,hcoeff,hh]

lemma exp_dyadic_bound {X : ℕ} (hX : 0 < X) {H : ℝ} (hH : H ≤ 1) :
    Real.exp (2*(Real.log (2*(X:ℝ))+H)) ≤ 4*Real.exp 2*(X:ℝ)^2 := by
  have hp : (0:ℝ) < 2*(X:ℝ) := by positivity
  have hh : Real.exp (2*(Real.log (2*(X:ℝ))+H)) ≤
      Real.exp (2*Real.log (2*(X:ℝ))+2) := by
    apply Real.exp_le_exp.mpr
    linarith only [hH]
  have he : Real.exp (2*Real.log (2*(X:ℝ)))=(2*(X:ℝ))^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hp]
    ring
  rw [Real.exp_add,he] at hh
  convert hh using 1
  ring

theorem dyadic_physical_window_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc X (2*X))
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) (Real.log y)‖) < ε*D*X := by
  let C := 4*Real.exp 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hL⟩ := dyadic_weighted_sharp_small hf hm hNP hd χ (div_pos hε hC)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt D
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hX0X hXp
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hDX : D ≤ (X:ℝ) := hX0.le.trans (by exact_mod_cast hX0X)
  have hH : D/(X:ℝ) ≤ 1 := (div_le_one hXr).mpr hDX
  have hu : ∀n∈Finset.Ioc X (2*X),Real.log (n:ℝ) ≤ Real.log (2*(X:ℝ)) := by
    intro n hn
    apply Real.log_le_log
    · exact_mod_cast ((show 0 < X by omega).trans (Finset.mem_Ioc.mp hn).1)
    · exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hb := sharp_physical_integral_bound (Ioc X (2*X))
    (characterModulation f χ) (fun n=>Real.log n) hu hLX.1
  have hmass : 0 ≤ ∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc X (2*X))
      (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖ := by
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  have hfac := mul_le_mul_of_nonneg_right (exp_dyadic_bound (show 0 < X by omega) hH) hmass
  have hfin := mul_lt_mul_of_pos_left hLX.2 (show 0 < C*(X:ℝ)^2 by positivity)
  have he : C*(X:ℝ)^2*((ε/C)*(D/(X:ℝ)))=ε*D*X := by field_simp
  rw [he] at hfin
  exact (hb.trans hfac).trans_lt hfin

end OrdinaryChainScales

end

end OAI
