import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicWeightRemoval
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogBorderCard
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpWindowIocAdd

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
lemma dyadic_subinterval_sharp_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      ∀A B : ℕ,X ≤ A → A ≤ B → B ≤ 2*X →
      (∫x : ℝ,‖sharpWindow (Ioc A B) (fun n=>characterModulation f χ n/(n:ℂ))
        (fun n=>Real.log n) (D/(X:ℝ)) x‖) < ε*(D/(X:ℝ)) := by
  obtain ⟨D0,hD0,hL⟩ := dyadic_prefix_sharp_small hf hm hNP hd χ (by positivity : 0 < ε/2)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  filter_upwards [hL D hD] with X hLX
  intro A B hXA hAB hB
  have hh := sharpWindow_Ioc_l1 (fun n=>characterModulation f χ n/(n:ℂ))
    (fun n=>Real.log n) (D/(X:ℝ)) hXA hAB
  have h1 := hLX A hXA (hAB.trans hB)
  have h2 := hLX B (hXA.trans hAB) hB
  linarith only [hh,h1,h2]

lemma subinterval_weight_removal {f : ℕ→ℂ} {d : ℕ} (χ : DirichletCharacter ℂ d)
    {A B : ℕ} {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun x : ℝ=>Real.exp (-x)*
      ‖sharpWindow (Ioc A B) (characterModulation f χ) (fun n=>Real.log n) H x‖) ∧
    (∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc A B)
      (characterModulation f χ) (fun n=>Real.log n) H x‖) ≤
      (∫x : ℝ,‖sharpWindow (Ioc A B)
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) H x‖)+
      H^2*(∑n∈Ioc A B,‖characterModulation f χ n/(n:ℂ)‖) := by
  have he : sharpWindow (Ioc A B)
      (fun n=>(characterModulation f χ n/(n:ℂ))*(Real.exp (Real.log n):ℂ))
      (fun n=>Real.log n) H =
      sharpWindow (Ioc A B) (characterModulation f χ) (fun n=>Real.log n) H := by
    ext x
    apply sum_congr rfl
    intro n hn
    have hnp : 0 < n := lt_of_le_of_lt (Nat.zero_le A) (mem_Ioc.mp hn).1
    have hnr : (0:ℝ) < n := by exact_mod_cast hnp
    dsimp only
    rw [Real.exp_log hnr,Complex.ofReal_natCast,div_mul_cancel₀ _ (by exact_mod_cast hnp.ne')]
  have hh := sharp_weight_removal (Ioc A B)
    (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) hH
  simpa only [he] using hh

lemma subinterval_coefficient_sum {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X A B : ℕ} (hX : 0 < X)
    (hXA : X ≤ A) (hB : B ≤ 2*X) :
    (∑n∈Ioc A B,‖characterModulation f χ n/(n:ℂ)‖) ≤ 1 := by
  apply le_trans _ (dyadic_coefficient_sum hf χ hX)
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_Ioc.mpr ⟨hXA.trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hB⟩
  · intro n hn hnn
    exact norm_nonneg _

lemma dyadic_subinterval_weighted_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      ∀A B : ℕ,X ≤ A → A ≤ B → B ≤ 2*X →
      Integrable (fun x : ℝ=>Real.exp (-x)*‖sharpWindow (Ioc A B)
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖) ∧
      (∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc A B)
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖) < ε*(D/(X:ℝ)) := by
  obtain ⟨D0,hD0,hL⟩ := dyadic_subinterval_sharp_small hf hm hNP hd χ (by positivity : 0 < ε/2)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0 : (0:ℝ) < D0).trans_le hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt (2*D/ε)
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hX0X hXp
  intro A B hXA hAB hB
  have hX : 0 < X := by omega
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hH : 0 < D/(X:ℝ) := div_pos hDp hXr
  have hsmall : D/(X:ℝ) < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp (hX0.trans_le (show (X0:ℝ) ≤ (X:ℝ) by exact_mod_cast hX0X))
    apply (div_lt_iff₀ hXr).2
    linarith only [hh]
  obtain ⟨hi,hbound⟩ := subinterval_weight_removal χ hH.le (A:=A) (B:=B) (f:=f)
  have hcoeff := mul_le_mul_of_nonneg_left
    (subinterval_coefficient_sum hf χ hX hXA hB) (sq_nonneg (D/(X:ℝ)))
  refine ⟨hi,?_⟩
  have hh := mul_lt_mul_of_pos_right hsmall hH
  have hLXAB := hLX A B hXA hAB hB
  nlinarith only [hbound,hLXAB,hcoeff,hh]

lemma dyadic_subinterval_physical_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      ∀A B : ℕ,X ≤ A → A ≤ B → B ≤ 2*X →
      (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc A B)
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) (Real.log y)‖) < ε*D*X := by
  let C := 4*Real.exp 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hL⟩ := dyadic_subinterval_weighted_small hf hm hNP hd χ (div_pos hε hC)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt D
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hX0X hXp
  intro A B hXA hAB hB
  have hX : 0 < X := by omega
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hDX : D ≤ (X:ℝ) := hX0.le.trans (by exact_mod_cast hX0X)
  have hH : D/(X:ℝ) ≤ 1 := (div_le_one hXr).mpr hDX
  have hu : ∀n∈Finset.Ioc A B,Real.log (n:ℝ) ≤ Real.log (2*(X:ℝ)) := by
    intro n hn
    apply Real.log_le_log
    · exact_mod_cast (hX.trans_le hXA).trans (Finset.mem_Ioc.mp hn).1
    · exact_mod_cast (Finset.mem_Ioc.mp hn).2.trans hB
  have hLAB := hLX A B hXA hAB hB
  have hb := sharp_physical_integral_bound (Ioc A B)
    (characterModulation f χ) (fun n=>Real.log n) hu hLAB.1
  have hmass : 0 ≤ ∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc A B)
      (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖ := by
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  have hfac := mul_le_mul_of_nonneg_right (exp_dyadic_bound hX hH) hmass
  have hfin := mul_lt_mul_of_pos_left hLAB.2 (show 0 < C*(X:ℝ)^2 by positivity)
  have he : C*(X:ℝ)^2*((ε/C)*(D/(X:ℝ)))=ε*D*X := by field_simp
  rw [he] at hfin
  exact (hb.trans hfac).trans_lt hfin

end OrdinaryChainScales

end

end OAI
