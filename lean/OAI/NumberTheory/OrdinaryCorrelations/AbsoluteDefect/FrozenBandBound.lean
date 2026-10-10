import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicSubintervalSharpSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxMono
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FrozenWidthError

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
lemma frozen_band_bound {f : ℕ→ℂ} (hf : OneBounded f) {d : ℕ}
    (χ : DirichletCharacter ℂ d) {X k j : ℕ} (hX : 0 < X) (hk : 0 < k)
    (hj : j < k) {D : ℝ} (hD : 0 ≤ D) (hDX : D ≤ (X:ℝ)) :
    (∫x : ℝ,‖sharpWindow (Ioc (bandCut X k j) (bandCut X k (j+1)))
      (characterModulation f χ) (fun n=>(n:ℝ)) D x‖) ≤
    (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc (bandCut X k j) (bandCut X k (j+1)))
      (characterModulation f χ) (fun n=>Real.log n) ((D/(1+(j:ℝ)/k))/(X:ℝ)) (Real.log y)‖)+
      (((Finset.Ioc (bandCut X k j) (bandCut X k (j+1))).card:ℝ)*(D/k+2*D^2/X)) := by
  let s := Finset.Ioc (bandCut X k j) (bandCut X k (j+1))
  let H := (D/(1+(j:ℝ)/k))/(X:ℝ)
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hc : 1 ≤ 1+(j:ℝ)/k := le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) hkr.le)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hnpos : ∀n∈s,(0:ℝ) < n := by
    intro n hn
    exact_mod_cast hX.trans_le (bandCut_lower X k j) |>.trans (Finset.mem_Ioc.mp hn).1
  have hW : ∀n∈s,0 ≤ (n:ℝ)*(Real.exp H-1) := by
    intro n hn
    exact mul_nonneg (hnpos n hn).le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hH))
  have hb := fixedWindow_l1_bound s (characterModulation f χ) (fun n=>(n:ℝ))
    (fun n=>(n:ℝ)*(Real.exp H-1)) hD hW
  have he := physicalWindow_integral_eq s (characterModulation f χ) (fun n=>(n:ℝ)) hnpos H
  rw [← he] at hb
  apply hb.trans
  apply _root_.add_le_add le_rfl
  calc
    _ ≤ ∑n∈s,(D/k+2*D^2/X) := by
      apply sum_le_sum
      intro n hn
      have hn0 := bandCut_real_lower hk (mem_Ioc.mp hn).1
      have hn1 : (n:ℝ) ≤ (1+(j:ℝ)/k+1/(k:ℝ))*(X:ℝ) := by
        have hh := bandCut_real_upper X (j+1) hk
        have hnn : (n:ℝ) ≤ bandCut X k (j+1) := by exact_mod_cast (mem_Ioc.mp hn).2
        have heq : (1+((j+1:ℕ):ℝ)/k)*(X:ℝ)=(1+(j:ℝ)/k+1/(k:ℝ))*(X:ℝ) := by push_cast; ring
        rw [heq] at hh
        exact hnn.trans hh
      have hn2 : (n:ℝ) ≤ 2*(X:ℝ) := by
        exact_mod_cast (mem_Ioc.mp hn).2.trans (bandCut_upper X hk (by omega))
      have herr := frozen_width_error hXr hD hDX hc (by positivity : (0:ℝ) ≤ 1/(k:ℝ)) hn0 hn1 hn2
      have herr' : |D-(n:ℝ)*(Real.exp H-1)| ≤ D/k+2*D^2/X := by
        convert herr using 1; ring
      calc
        _ ≤ 1*(D/k+2*D^2/X) := mul_le_mul (characterModulation_bound hf χ n) herr'
          (abs_nonneg _) (by positivity)
        _ = _ := one_mul _
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; rfl

lemma finite_frozen_band_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (characterModulation f χ)
        (fun n=>(n:ℝ)) D x‖) ≤
        (k:ℝ)*ε*D*X+(X:ℝ)*(D/k+2*D^2/X) := by
  obtain ⟨E0,hE0,hL⟩ := dyadic_subinterval_physical_small hf hm hNP hd χ hε
  refine ⟨2*E0,by omega,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast (show 0 < 2*E0 by omega) : (0:ℝ) < (2*E0:ℕ)).trans_le hD
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hgate (j : ℕ) (hj : j∈range k) :
      (E0:ℝ) ≤ D/(1+(j:ℝ)/k) ∧ 1 ≤ 1+(j:ℝ)/k := by
    have hjr : (j:ℝ) ≤ k := by exact_mod_cast (mem_range.mp hj).le
    have hc : (j:ℝ)/k ≤ 1 := (div_le_one hkr).mpr hjr
    have hc0 : 1 ≤ 1+(j:ℝ)/k := le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) hkr.le)
    refine ⟨(le_div_iff₀ (by positivity)).mpr ?_,hc0⟩
    have hEr : (0:ℝ) ≤ E0 := by positivity
    push_cast at hD
    nlinarith only [hc,hD,hEr]
  have hall : ∀ᶠ X : ℕ in atTop,∀j∈range k,
      ∀A B : ℕ,X ≤ A → A ≤ B → B ≤ 2*X →
      (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc A B) (characterModulation f χ)
        (fun n=>Real.log n) ((D/(1+(j:ℝ)/k))/(X:ℝ)) (Real.log y)‖) < ε*(D/(1+(j:ℝ)/k))*X := by
    apply (eventually_all_finset (range k)).mpr
    intro j hj
    exact hL _ (hgate j hj).1
  obtain ⟨X0,hX0⟩ := exists_nat_gt D
  filter_upwards [hall,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hallX hXX0 hXp
  have hX : 0 < X := by omega
  have hDX : D ≤ (X:ℝ) := hX0.le.trans (by exact_mod_cast hXX0)
  apply (sharpWindow_partition_l1 (characterModulation f χ) (fun n=>(n:ℝ)) D X hk).trans
  calc
    _ ≤ ∑j∈range k,(ε*D*X+
        ((Finset.Ioc (bandCut X k j) (bandCut X k (j+1))).card:ℝ)*(D/k+2*D^2/X)) := by
      apply sum_le_sum
      intro j hj
      have hjk := mem_range.mp hj
      apply (frozen_band_bound hf χ hX hk hjk hDp.le hDX).trans
      apply _root_.add_le_add _ le_rfl
      have hh := hallX j hj (bandCut X k j) (bandCut X k (j+1))
        (bandCut_lower X k j) (bandCut_mono X k (Nat.le_succ j))
        (bandCut_upper X hk (by omega))
      have hdj := div_le_self hDp.le (hgate j hj).2
      exact hh.le.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdj hε.le)
        (Nat.cast_nonneg X))
    _ = _ := by
      rw [sum_add_distrib,← sum_mul (range k) (fun j=>((Finset.Ioc (bandCut X k j) (bandCut X k (j+1))).card:ℝ)) (D/k+2*D^2/X),band_card_sum X hk]
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring

theorem dyadic_character_fixed_window_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (characterModulation f χ)
        (fun n=>(n:ℝ)) D x‖) < ε*D*X := by
  obtain ⟨k,hkε⟩ := exists_nat_gt (8/ε)
  have hk : 0 < k := by
    have hkp : (0:ℝ) < k := (by positivity : (0:ℝ) < 8/ε).trans hkε
    exact_mod_cast hkp
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨D0,hD0,hL⟩ := finite_frozen_band_small hf hm hNP hd χ
    (by positivity : 0 < ε/(4*k)) hk
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0 : (0:ℝ) < D0).trans_le hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt (8*D/ε)
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hXX0 hXp
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hkbound : 1/(k:ℝ) < ε/8 := by
    have hh := (div_lt_iff₀ hε).mp hkε
    apply (div_lt_iff₀ hkr).mpr
    nlinarith only [hh]
  have hXbound : 2*D^2 < ε*D*X/4 := by
    have hh0 := hX0.trans_le (show (X0:ℝ) ≤ X by exact_mod_cast hXX0)
    have hh := (div_lt_iff₀ hε).mp hh0
    have hp := mul_lt_mul_of_pos_right hh hDp
    nlinarith only [hp]
  have he : (k:ℝ)*(ε/(4*k))*D*X+(X:ℝ)*(D/k+2*D^2/X)=
      ε*D*X/4+(1/(k:ℝ))*(D*X)+2*D^2 := by field_simp; ring
  rw [he] at hLX
  have hsmall := mul_lt_mul_of_pos_right hkbound (mul_pos hDp hXr)
  have hpositive : 0 < ε*D*X := mul_pos (mul_pos hε hDp) hXr
  linarith only [hLX,hsmall,hXbound,hpositive]

end OrdinaryChainScales

end

end OAI
