import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpSmoothingNumeric
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrefixSet

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

lemma log_border_card {X A : ℕ} (hX : 0 < X) (hXA : X ≤ A) (hA : A ≤ 2*X)
    {D : ℝ} (hD : 0 ≤ D) :
    (borderSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A) (D/(X:ℝ))).card ≤
      Nat.ceil (2*D)+1 := by
  let R := Nat.ceil (2*D)
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hAr : (0:ℝ) < A := by exact_mod_cast hX.trans_le hXA
  have hsub : borderSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A) (D/(X:ℝ)) ⊆
      Icc (A-R) A := by
    intro n hn
    obtain ⟨hnbase,hnlog⟩ := mem_filter.mp hn
    obtain ⟨hnX,hn2X⟩ := mem_Ioc.mp hnbase
    have hnr : (0:ℝ) < n := by exact_mod_cast hX.trans hnX
    have hnAr : (n:ℝ) ≤ A := (Real.log_le_log_iff hnr hAr).mp hnlog.2
    have hnA : n ≤ A := by exact_mod_cast hnAr
    have hsep := log_separation hAr hnr (show (A:ℝ) ≤ 2*(X:ℝ) by exact_mod_cast hA)
      (show (n:ℝ) ≤ 2*(X:ℝ) by exact_mod_cast hn2X)
    rw [abs_of_nonneg (sub_nonneg.mpr hnAr),abs_of_nonneg (sub_nonneg.mpr hnlog.2)] at hsep
    have hr : (A:ℝ)-(n:ℝ) < 2*D := by
      have hs : ((A:ℝ)-(n:ℝ))/(2*(X:ℝ)) < D/(X:ℝ) := hsep.trans_lt (by linarith [hnlog.1])
      have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(X:ℝ))).mp hs
      have he : D/(X:ℝ)*(2*(X:ℝ))=2*D := by field_simp
      rwa [he] at hh
    have hm : A-n ≤ R := by
      have hh : ((A-n:ℕ):ℝ) ≤ (R:ℝ) := by
        rw [Nat.cast_sub hnA]
        dsimp only [R]
        rw [natCast_ceil_eq_intCast_ceil (mul_nonneg (by norm_num) hD)]
        exact hr.le.trans (Int.le_ceil _)
      exact_mod_cast hh
    exact mem_Icc.mpr ⟨by omega,hnA⟩
  apply (Finset.card_le_card hsub).trans
  simp only [Nat.card_Icc]
  dsimp only [R]
  omega

lemma dyadic_coefficient_bound {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X n : ℕ} (hX : 0 < X) (hnX : X ≤ n) :
    ‖characterModulation f χ n/(n:ℂ)‖ ≤ (X:ℝ)⁻¹ := by
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hnr : (0:ℝ) < n := by exact_mod_cast hX.trans_le hnX
  have hnXr : (X:ℝ) ≤ n := by exact_mod_cast hnX
  rw [norm_div,Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (characterModulation_bound hf χ n) hnr.le).trans
    (by simpa only [one_div] using inv_le_inv₀ hnr hXr |>.2 hnXr)

lemma log_border_mass {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X A : ℕ}
    (hX : 0 < X) (hXA : X ≤ A) (hA : A ≤ 2*X) {D : ℝ} (hD : 0 ≤ D) :
    (∑n∈borderSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A) (D/(X:ℝ)),
      ‖characterModulation f χ n/(n:ℂ)‖) ≤ ((Nat.ceil (2*D):ℝ)+1)/(X:ℝ) := by
  calc
    _ ≤ ∑n∈borderSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A) (D/(X:ℝ)),
        (X:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      exact dyadic_coefficient_bound hf χ hX (mem_Ioc.mp (mem_filter.mp hn).1).1.le
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      have hc : ((borderSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A) (D/(X:ℝ))).card:ℝ) ≤
          (Nat.ceil (2*D):ℝ)+1 := by exact_mod_cast log_border_card hX hXA hA hD
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ (X:ℝ)⁻¹)

lemma log_prefixSet {X A : ℕ} (hX : 0 < X) (hXA : X ≤ A) (hA : A ≤ 2*X) :
    prefixSet (Ioc X (2*X)) (fun n=>Real.log n) (Real.log A)=Finset.Ioc X A := by
  ext n
  simp only [prefixSet,mem_filter,Finset.mem_Ioc]
  have hAr : (0:ℝ) < A := by exact_mod_cast hX.trans_le hXA
  constructor
  · rintro ⟨⟨hnX,hn2X⟩,hnlog⟩
    have hnr : (0:ℝ) < n := by exact_mod_cast hX.trans hnX
    exact ⟨hnX,by exact_mod_cast (Real.log_le_log_iff hnr hAr).mp hnlog⟩
  · rintro ⟨hnX,hnA⟩
    refine ⟨⟨hnX,hnA.trans hA⟩,?_⟩
    apply Real.log_le_log
    · exact_mod_cast hX.trans hnX
    · exact_mod_cast hnA

lemma dyadic_prefix_sharp_bound {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X A : ℕ}
    (hX : 0 < X) (hXA : X ≤ A) (hA : A ≤ 2*X) {D : ℝ} (hD : 0 ≤ D) :
    (∫x : ℝ,‖sharpWindow (Ioc X A) (fun n=>characterModulation f χ n/(n:ℂ))
      (fun n=>Real.log n) (D/(X:ℝ)) x‖) ≤
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (fun n=>characterModulation f χ n/(n:ℂ))
      (fun n=>Real.log n) (D/(X:ℝ)) x‖)+(D/(X:ℝ))*(((Nat.ceil (2*D):ℝ)+1)/(X:ℝ)) := by
  have hh := prefixWindow_l1_bound (Ioc X (2*X))
    (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (Real.log A)
    (div_nonneg hD (Nat.cast_nonneg X))
  rw [log_prefixSet hX hXA hA] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (log_border_mass hf χ hX hXA hA hD)
    (div_nonneg hD (Nat.cast_nonneg X))))

lemma dyadic_prefix_sharp_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      ∀A : ℕ,X ≤ A → A ≤ 2*X →
      (∫x : ℝ,‖sharpWindow (Ioc X A) (fun n=>characterModulation f χ n/(n:ℂ))
        (fun n=>Real.log n) (D/(X:ℝ)) x‖) < ε*(D/(X:ℝ)) := by
  obtain ⟨D0,hD0,hL⟩ := dyadic_sharp_log_window_small hf hm hNP hd χ (by positivity : 0 < ε/2)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0 : (0:ℝ) < D0).trans_le hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt (2*((Nat.ceil (2*D):ℝ)+1)/ε)
  filter_upwards [hL D hD,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hLX hX0X hXp
  intro A hXA hA
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hH : 0 < D/(X:ℝ) := div_pos hDp hXr
  have hsmall : ((Nat.ceil (2*D):ℝ)+1)/(X:ℝ) < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp (hX0.trans_le (show (X0:ℝ) ≤ (X:ℝ) by exact_mod_cast hX0X))
    apply (div_lt_iff₀ hXr).2
    linarith only [hh]
  have hbound := dyadic_prefix_sharp_bound hf χ (show 0 < X by omega) hXA hA hDp.le
  have herr := mul_lt_mul_of_pos_left hsmall hH
  linarith only [hbound,hLX,herr]

end OrdinaryChainScales

end

end OAI
