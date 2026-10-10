import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicSubintervalSharpSmall

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

namespace OrdinaryMellinModulus
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open OrdinaryGaussianWindow OrdinarySharpWindow OrdinaryChainScales Finset Filter MeasureTheory

def sharpLogGate (A c k m : ℕ) : ℝ :=
  ((16*(2*(m+k)+2+c+1)*2^(2^(29*(2*(m+k)+2+3)+A)):ℕ):ℝ) /
    ((1/2:ℝ)^m*bumpMass/(8*(bumpMoment+1)))

lemma sharpLogGate_pos (A c k m : ℕ) : 0<sharpLogGate A c k m := by
  have hb := bumpMass_pos
  have hm := bumpMoment_nonneg
  unfold sharpLogGate
  positivity

lemma log_to_subinterval_physical {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {η D : ℝ} (hη : 0<η) (hD : 0<D)
    (hL : ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
        < η*(D/(X:ℝ))) :
    ∀ᶠ X : ℕ in atTop, ∀ A B : ℕ, X≤A → A≤B → B≤2*X →
      (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc A B) (characterModulation f χ)
        (fun n=>Real.log n) (D/(X:ℝ)) (Real.log y)‖) <
          (20*Real.exp 2)*η*D*X := by
  obtain ⟨X0,hX0⟩ := exists_nat_gt (((Nat.ceil (2*D):ℝ)+1)/η)
  obtain ⟨X1,hX1⟩ := exists_nat_gt (D/η)
  obtain ⟨X2,hX2⟩ := exists_nat_gt D
  filter_upwards [hL,eventually_ge_atTop X0,eventually_ge_atTop X1,
    eventually_ge_atTop X2,eventually_ge_atTop (1:ℕ)] with X hLX hXX0 hXX1 hXX2 hXp
  have hX : 0<X := by omega
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hH : 0<D/(X:ℝ) := div_pos hD hXr
  have hDX : D≤(X:ℝ) := hX2.le.trans (by exact_mod_cast hXX2)
  have hb : ((Nat.ceil (2*D):ℝ)+1)/(X:ℝ)<η := by
    apply (div_lt_iff₀ hXr).mpr
    have ht := (div_lt_iff₀ hη).mp (hX0.trans_le (show (X0:ℝ)≤(X:ℝ) by exact_mod_cast hXX0))
    linarith only [ht]
  have hh : D/(X:ℝ)<η := by
    apply (div_lt_iff₀ hXr).mpr
    have ht := (div_lt_iff₀ hη).mp (hX1.trans_le (show (X1:ℝ)≤(X:ℝ) by exact_mod_cast hXX1))
    linarith only [ht]
  have hp (A : ℕ) (hXA : X≤A) (hA : A≤2*X) :
      (∫x : ℝ,‖sharpWindow (Ioc X A)
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
        < 2*η*(D/(X:ℝ)) := by
    have hbound := dyadic_prefix_sharp_bound hf χ hX hXA hA hD.le
    have herr := mul_lt_mul_of_pos_left hb hH
    linarith only [hbound,hLX,herr]
  intro A B hXA hAB hB
  have hsub := sharpWindow_Ioc_l1 (fun n=>characterModulation f χ n/(n:ℂ))
    (fun n=>Real.log n) (D/(X:ℝ)) hXA hAB
  have hsubsmall : (∫x : ℝ,‖sharpWindow (Ioc A B)
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
        < 4*η*(D/(X:ℝ)) := by
    have ha := hp A hXA (hAB.trans hB)
    have hb := hp B (hXA.trans hAB) hB
    linarith only [hsub,ha,hb]
  obtain ⟨hi,hbound⟩ := subinterval_weight_removal χ hH.le (A:=A) (B:=B) (f:=f)
  have hc := mul_le_mul_of_nonneg_left (subinterval_coefficient_sum hf χ hX hXA hB)
    (sq_nonneg (D/(X:ℝ)))
  have he := mul_lt_mul_of_pos_right hh hH
  have hweighted : (∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc A B)
        (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
        < 5*η*(D/(X:ℝ)) := by
    nlinarith only [hbound,hc,he,hsubsmall]
  have hu : ∀n∈Finset.Ioc A B,Real.log (n:ℝ)≤Real.log (2*(X:ℝ)) := by
    intro n hn
    apply Real.log_le_log
    · exact_mod_cast (hX.trans_le hXA).trans (Finset.mem_Ioc.mp hn).1
    · exact_mod_cast (Finset.mem_Ioc.mp hn).2.trans hB
  have hphys := sharp_physical_integral_bound (Ioc A B)
    (characterModulation f χ) (fun n=>Real.log n) hu hi
  have hmass : 0≤∫x : ℝ,Real.exp (-x)*‖sharpWindow (Ioc A B)
      (characterModulation f χ) (fun n=>Real.log n) (D/(X:ℝ)) x‖ := by
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  have hfac := mul_le_mul_of_nonneg_right (exp_dyadic_bound hX ((div_le_one hXr).mpr hDX)) hmass
  have hfin := mul_lt_mul_of_pos_left hweighted (by positivity : 0<4*Real.exp 2*(X:ℝ)^2)
  have heq : (4*Real.exp 2*(X:ℝ)^2)*(5*η*(D/(X:ℝ)))=(20*Real.exp 2)*η*D*X := by
    field_simp
    ring
  rw [heq] at hfin
  exact (hphys.trans hfac).trans_lt hfin

end OrdinaryMellinModulus

end

end OAI
