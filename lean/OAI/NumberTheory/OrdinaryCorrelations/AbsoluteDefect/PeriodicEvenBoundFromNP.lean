import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WindowBound

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
open OrdinaryCorrelations.LocalExpansion OrdinaryCorrelations.ResidueCharacters

lemma periodic_even_bound_from_NP {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {q m : ℕ} (hq : 0<q) (hqm : q≤2^(10*m)) (w : ℕ→ℂ) (hw : OneBounded w)
    {η D : ℝ} (hη : 0≤η) (hD : 0≤D)
    (hbase : ∀g : ℕ→ℂ,OneBounded g → Multiplicative g → UniformlyNonpretentious g → WindowBound g η D) :
    WindowBound (fun n=>f n*w (n%q)) ((2:ℝ)^(13*m+16)*η) D := by
  let t : ℝ := (2:ℝ)^(3*m+16)*η
  have ht : 0≤t := by dsimp [t]; positivity
  have hsmall (b : ℕ) : WindowBound
      (fun n=>w b*(f n*(if n ≡ b [MOD q] then (1:ℂ) else 0))) t D := by
    have hc0 := primeFactors_card_le_dyadic (Nat.gcd_pos_of_pos_right b hq)
      ((Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)).trans hqm)
    have hc : (b.gcd q).primeFactors.card≤3*m+16 := by omega
    have he : (2:ℝ)^(b.gcd q).primeFactors.card≤(2:ℝ)^(3*m+16) :=
      pow_le_pow_right₀ (by norm_num) hc
    have hbudget : (2:ℝ)^(b.gcd q).primeFactors.card*η≤t :=
      mul_le_mul_of_nonneg_right he hη
    have hr := windowBound_mono hD hbudget (residue_bound_from_NP hf hm hNP hq b hη hD hbase)
    exact windowBound_mono hD (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw b) ht)
      (windowBound_const_mul (w b) hr)
  have hs := windowBound_finsetSum (range q)
    (fun b n=>w b*(f n*(if n ≡ b [MOD q] then (1:ℂ) else 0))) (fun _=>t) D
    (fun b _=>hsmall b)
  have he : (∑_b∈range q,t)≤(2:ℝ)^(13*m+16)*η := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    have hqr : (q:ℝ)≤(2:ℝ)^(10*m) := by exact_mod_cast hqm
    calc
      _ ≤ (2:ℝ)^(10*m)*t := mul_le_mul_of_nonneg_right hqr ht
      _ = _ := by dsimp [t]; rw [←mul_assoc,←pow_add]; congr 2; omega
  apply windowBound_congr_pos _ (windowBound_mono hD he hs)
  intro n hn
  exact (finite_residue_expansion f w hq n).symm

theorem periodic_even_power_logarithmic :
    ∃ A c k v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {q : ℕ}, 0<q → q≤2^(10*m) → ∀w : ℕ→ℂ, OneBounded w →
      ∀D : ℝ, 2*sharpLogGate A c k (30*m+v)≤D →
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*w (n%q)) (fun n=>(n:ℝ)) D x‖)
      ≤ (1/2:ℝ)^(2*m)*D*X := by
  obtain ⟨A,c,k,v,hP⟩ := dyadic_physical_power_logarithmic
  refine ⟨A,c,k,40+v,?_⟩
  intro m f hf hm hNP q hq hqm w hw D hD
  let η : ℝ := (1/2:ℝ)^(15*m+20)
  have hη : 0≤η := by dsimp [η]; positivity
  have hDp : 0<D := by
    have ht := sharpLogGate_pos A c k (30*m+(40+v))
    linarith only [ht,hD]
  have hbase (g : ℕ→ℂ) (hg : OneBounded g) (hgm : Multiplicative g)
      (hgn : UniformlyNonpretentious g) : WindowBound g η D := by
    have he : characterModulation g (1:DirichletCharacter ℂ 1)=g := by
      funext n
      have hn : (n:ZMod 1)=1 := Subsingleton.elim _ _
      simp [characterModulation,hn]
    have hgate : 2*sharpLogGate A c k (2*(15*m+20)+v)≤D := by
      convert hD using 1; congr 2; omega
    have hL := hP (15*m+20) hg hgm hgn (by decide : 0<(1:ℕ)) (1:DirichletCharacter ℂ 1) D hgate
    filter_upwards [hL] with X hLX
    simpa only [he] using hLX.le
  have hs := periodic_even_bound_from_NP hf hm hNP hq hqm w hw hη hDp.le hbase
  have hbudget : (2:ℝ)^(13*m+16)*η≤(1/2:ℝ)^(2*m) := by
    have hp : (2:ℝ)^(13*m+16)*(1/2:ℝ)^(13*m+16)=1 := by rw [←mul_pow]; norm_num
    dsimp [η]
    rw [show 15*m+20=(13*m+16)+(2*m+4) by omega,
      pow_add (1/2:ℝ) (13*m+16) (2*m+4),←mul_assoc,hp,one_mul,pow_add]
    norm_num only [show (1/2:ℝ)^4=1/16 by norm_num]
    nlinarith only [show 0≤(1/2:ℝ)^(2*m) by positivity]
  exact windowBound_mono hDp.le hbudget hs

end OrdinaryMellinModulus

end

end OAI
