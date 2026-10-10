import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicSharpLogPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FrozenBandBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpLogGate

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

theorem dyadic_physical_power_logarithmic :
    ∃ A c k v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀D : ℝ, 2*sharpLogGate A c k (2*m+v)≤D →
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (characterModulation f χ) (fun n=>(n:ℝ)) D x‖)
      < (1/2:ℝ)^m*D*X := by
  obtain ⟨A,c,k,hL⟩ := dyadic_sharp_log_power_logarithmic
  let C : ℝ := 20*Real.exp 2
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨v,hv⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ)<1/(128*C))
    (by norm_num : (1/2:ℝ)<1)
  refine ⟨A,c,k,v,?_⟩
  intro m f hf hm hNP d hd χ D hD
  let ε : ℝ := (1/2:ℝ)^m
  let η : ℝ := (1/2:ℝ)^(2*m+v)
  let K : ℕ := 2^(m+4)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hη : 0<η := by dsimp [η]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hG := sharpLogGate_pos A c k (2*m+v)
  have hDp : 0<D := by linarith only [hG,hD]
  have hgate (j : ℕ) (hj : j∈range K) :
      sharpLogGate A c k (2*m+v)≤D/(1+(j:ℝ)/K) ∧ 1≤1+(j:ℝ)/K := by
    have hjr : (j:ℝ)≤K := by exact_mod_cast (mem_range.mp hj).le
    have hc : (j:ℝ)/K≤1 := (div_le_one hKr).mpr hjr
    have hc0 : 1≤1+(j:ℝ)/K := le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) hKr.le)
    refine ⟨(le_div_iff₀ (by positivity)).mpr ?_,hc0⟩
    nlinarith only [hc,hD,hG]
  have hall : ∀ᶠ X : ℕ in atTop,∀j∈range K,
      ∀A' B : ℕ,X≤A' → A'≤B → B≤2*X →
      (∫y in Set.Ioi (0:ℝ),‖sharpWindow (Ioc A' B) (characterModulation f χ)
        (fun n=>Real.log n) ((D/(1+(j:ℝ)/K))/(X:ℝ)) (Real.log y)‖)
        < C*η*(D/(1+(j:ℝ)/K))*X := by
    apply (eventually_all_finset (range K)).mpr
    intro j hj
    apply log_to_subinterval_physical hf χ hη (div_pos hDp (by positivity))
    exact hL (2*m+v) hf hm hNP hd χ _ (hgate j hj).1
  obtain ⟨X0,hX0⟩ := exists_nat_gt D
  obtain ⟨X1,hX1⟩ := exists_nat_gt (8*D/ε)
  filter_upwards [hall,eventually_ge_atTop X0,eventually_ge_atTop X1,
    eventually_ge_atTop (1:ℕ)] with X hallX hXX0 hXX1 hXp
  have hX : 0<X := by omega
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hDX : D≤(X:ℝ) := hX0.le.trans (by exact_mod_cast hXX0)
  have hb : (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (characterModulation f χ)
        (fun n=>(n:ℝ)) D x‖) ≤
        (K:ℝ)*(C*η)*D*X+(X:ℝ)*(D/K+2*D^2/X) := by
    apply (sharpWindow_partition_l1 (characterModulation f χ) (fun n=>(n:ℝ)) D X hK).trans
    calc
      _ ≤ ∑j∈range K,(C*η*D*X+
          ((Finset.Ioc (bandCut X K j) (bandCut X K (j+1))).card:ℝ)*(D/K+2*D^2/X)) := by
        apply sum_le_sum
        intro j hj
        have hjK := mem_range.mp hj
        apply (frozen_band_bound hf χ hX hK hjK hDp.le hDX).trans
        apply _root_.add_le_add _ le_rfl
        have hh := hallX j hj (bandCut X K j) (bandCut X K (j+1))
          (bandCut_lower X K j) (bandCut_mono X K (Nat.le_succ j))
          (bandCut_upper X hK (by omega))
        have hdj := div_le_self hDp.le (hgate j hj).2
        exact hh.le.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdj (mul_pos hC hη).le) (Nat.cast_nonneg X))
      _ = _ := by
        rw [sum_add_distrib,←sum_mul (range K) (fun j=>((Finset.Ioc (bandCut X K j) (bandCut X K (j+1))).card:ℝ)) (D/K+2*D^2/X),band_card_sum X hK]
        simp only [sum_const,card_range,nsmul_eq_mul]
        ring
  have hp : (2:ℝ)^m*(1/2:ℝ)^m=1 := by rw [←mul_pow]; norm_num
  have hcoe : (K:ℝ)=(2:ℝ)^(m+4) := by dsimp [K]; norm_cast
  have hpower : (K:ℝ)*(C*η)=16*C*(1/2:ℝ)^v*ε := by
    rw [hcoe]
    dsimp [η,ε]
    rw [show 2*m+v=m+(m+v) by omega,pow_add,pow_add,pow_add]
    norm_num only [show (2:ℝ)^4=16 by norm_num]
    calc
      _ = 16*C*((2:ℝ)^m*(1/2:ℝ)^m)*(1/2:ℝ)^v*(1/2:ℝ)^m := by ring
      _ = _ := by rw [hp]; ring
  have hsmall : (K:ℝ)*(C*η)<ε/8 := by
    rw [hpower]
    have ht := (lt_div_iff₀ (by positivity : (0:ℝ)<128*C)).mp hv
    have ht' : 16*C*(1/2:ℝ)^v<1/8 := by nlinarith only [ht]
    have hh := mul_lt_mul_of_pos_right ht' hε
    linarith only [hh]
  have hKinv : 1/(K:ℝ)=ε/16 := by
    apply (div_eq_iff hKr.ne').mpr
    rw [hcoe]
    dsimp [ε]
    rw [pow_add]
    norm_num only [show (2:ℝ)^4=16 by norm_num]
    symm
    calc
      _ = (2:ℝ)^m*(1/2:ℝ)^m := by ring
      _ = 1 := hp
  have hboundary : 2*D^2<ε*D*X/4 := by
    have ht := (div_lt_iff₀ hε).mp (hX1.trans_le (show (X1:ℝ)≤(X:ℝ) by exact_mod_cast hXX1))
    have hh := mul_lt_mul_of_pos_right ht hDp
    nlinarith only [hh]
  have heq : (K:ℝ)*(C*η)*D*X+(X:ℝ)*(D/K+2*D^2/X)=
      ((K:ℝ)*(C*η))*D*X+(1/(K:ℝ))*(D*X)+2*D^2 := by
    field_simp
    ring
  rw [heq,hKinv] at hb
  have hh := mul_lt_mul_of_pos_right hsmall (mul_pos hDp hXr)
  have hhpos : 0<ε*D*X := mul_pos (mul_pos hε hDp) hXr
  change _<ε*D*X
  nlinarith only [hb,hh,hboundary,hhpos]

end OrdinaryMellinModulus

end

end OAI
