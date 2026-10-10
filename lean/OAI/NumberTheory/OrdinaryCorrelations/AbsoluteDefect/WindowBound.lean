import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicPhysicalPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WindowMulBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeFactorsCardLeDyadic

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

def WindowBound (f : ℕ→ℂ) (η D : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop,
    (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) f (fun n=>(n:ℝ)) D x‖)≤η*D*X

lemma windowBound_congr_pos {f g : ℕ→ℂ} {η D : ℝ}
    (h : ∀n : ℕ,0<n → f n=g n) (hf : WindowBound f η D) : WindowBound g η D := by
  filter_upwards [hf] with X hX
  convert hX using 1
  congr 1
  funext x
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [h n (lt_of_le_of_lt (Nat.zero_le X) (mem_Ioc.mp hn).1)]

lemma windowBound_mono {f : ℕ→ℂ} {η η' D : ℝ} (hD : 0≤D)
    (hη : η≤η') (hf : WindowBound f η D) : WindowBound f η' D := by
  filter_upwards [hf] with X hX
  exact hX.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hη hD) (Nat.cast_nonneg X))

lemma windowBound_const_mul (c : ℂ) {f : ℕ→ℂ} {η D : ℝ}
    (hf : WindowBound f η D) : WindowBound (fun n=>c*f n) (‖c‖*η) D := by
  filter_upwards [hf] with X hX
  simp_rw [sharpWindow_const_mul,norm_mul]
  rw [MeasureTheory.integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hX (norm_nonneg c)
  simpa only [mul_assoc] using hh

lemma windowBound_add {f g : ℕ→ℂ} {η θ D : ℝ}
    (hf : WindowBound f η D) (hg : WindowBound g θ D) :
    WindowBound (fun n=>f n+g n) (η+θ) D := by
  filter_upwards [hf,hg] with X hX hY
  have hh := sharpWindow_add_l1 (Ioc X (2*X)) f g (fun n=>(n:ℝ)) D
  nlinarith only [hh,hX,hY]

lemma windowBound_finsetSum {ι : Type*} (S : Finset ι) (F : ι→ℕ→ℂ) (η : ι→ℝ) (D : ℝ)
    (hF : ∀i∈S,WindowBound (F i) (η i) D) :
    WindowBound (fun n=>∑i∈S,F i n) (∑i∈S,η i) D := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [] with X
    simp [sharpWindow]
  | @insert i S hi ih =>
    simp only [sum_insert hi]
    exact windowBound_add (hF i (mem_insert_self i S))
      (ih (fun j hj=>hF j (mem_insert_of_mem hj)))

lemma dilation_bound_from_NP {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d q : ℕ} (hd : 0<d) (hq : 0<q) (χ : DirichletCharacter ℂ q)
    {η D : ℝ}
    (hbase : ∀g : ℕ→ℂ,OneBounded g → Multiplicative g → UniformlyNonpretentious g → WindowBound g η D) :
    WindowBound (fun n=>f n*dilation d (fun k=>χ (k:ZMod q)) n)
      ((2:ℝ)^d.primeFactors.card*η) D := by
  let F : Finset ℕ→ℕ→ℂ := fun E n=>f n*dilationSummand d (fun k=>χ (k:ZMod q)) E n
  have hFb (E : Finset ℕ) : OneBounded (F E) :=
    window_mul_bounded hf (dilationSummand_bounded d _ (char_bounded χ) E)
  have hFm (E : Finset ℕ) : Multiplicative (F E) :=
    window_mul_multiplicative hm (dilationSummand_multiplicative d _ E)
  have hFnp (E : Finset ℕ) : UniformlyNonpretentious (F E) := by
    apply CharacterStability.finite_twist_nonpretentious hq χ f (F E) hf (hFb E)
      d.primeFactors _ hNP
    intro p hp hpd
    dsimp only [F]
    have he := dilationSummand_primePow d (fun k=>χ (k:ZMod q)) (by simp) E hp hpd 1
    simp only [pow_one] at he
    rw [he]
  have hsmall (E : Finset ℕ) : WindowBound (fun n=>(-1:ℂ)^E.card*F E n) η D := by
    simpa using windowBound_const_mul ((-1:ℂ)^E.card) (hbase (F E) (hFb E) (hFm E) (hFnp E))
  have hs := windowBound_finsetSum d.primeFactors.powerset
    (fun E n=>(-1:ℂ)^E.card*F E n) (fun _=>η) D (fun E _=>hsmall E)
  simp only [sum_const,card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hs
  apply windowBound_congr_pos _ hs
  intro n hn
  rw [dilation_expansion d hd _ (char_multiplicative χ) (by simp) hn,mul_sum]
  apply sum_congr rfl
  intro E hE
  dsimp only [F]
  ring

lemma char_coeff_sum_le_one {q : ℕ} (hq : 0<q) (b : ℕ) :
    (∑χ : DirichletCharacter ℂ q,‖(q.totient:ℂ)⁻¹*star (χ (b:ZMod q))‖)≤1 := by
  let : NeZero q := ⟨hq.ne'⟩
  have ht : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hc : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    rw [←Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  calc
    _ ≤ ∑χ : DirichletCharacter ℂ q,(q.totient:ℝ)⁻¹ := by
      apply sum_le_sum
      intro χ hχ
      simp only [norm_mul,norm_inv,norm_natCast,norm_star]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one (b:ZMod q)) (inv_nonneg.mpr ht.le)
    _ = 1 := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]
      exact mul_inv_cancel₀ ht.ne'

lemma residue_bound_from_NP {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {l : ℕ} (hl : 0<l) (b : ℕ) {η D : ℝ} (hη : 0≤η) (hD : 0≤D)
    (hbase : ∀g : ℕ→ℂ,OneBounded g → Multiplicative g → UniformlyNonpretentious g → WindowBound g η D) :
    WindowBound (fun n=>f n*(if n ≡ b [MOD l] then (1:ℂ) else 0))
      ((2:ℝ)^(b.gcd l).primeFactors.card*η) D := by
  let d := b.gcd l
  let q := l/d
  have hd : 0<d := Nat.gcd_pos_of_pos_right b hl
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_right b l)) hd
  let a (χ : DirichletCharacter ℂ q) : ℂ := (q.totient:ℂ)⁻¹*star (χ ((b/d):ZMod q))
  let F (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := f n*dilation d (fun k=>χ (k:ZMod q)) n
  let t : ℝ := (2:ℝ)^d.primeFactors.card*η
  have hsmall (χ : DirichletCharacter ℂ q) : WindowBound (fun n=>a χ*F χ n) (‖a χ‖*t) D :=
    windowBound_const_mul (a χ) (dilation_bound_from_NP hf hm hNP hd hq χ hbase)
  have hs := windowBound_finsetSum univ (fun χ n=>a χ*F χ n) (fun χ=>‖a χ‖*t) D (fun χ _=>hsmall χ)
  have hweights : (∑χ : DirichletCharacter ℂ q,‖a χ‖*t)≤t := by
    rw [←sum_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (char_coeff_sum_le_one hq (b/d))
      (show 0≤t by dsimp [t]; positivity)
  have hs' := windowBound_mono hD hweights hs
  apply windowBound_congr_pos _ hs'
  intro n hn
  rw [gcd_indicator l b n hl,mul_sum,mul_sum]
  apply sum_congr rfl
  intro χ hχ
  dsimp only [a,F,d,q]
  ring

lemma periodic_bound_from_NP {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {q m : ℕ} (hq : 0<q) (hqm : q≤2^(5*m)) (w : ℕ→ℂ) (hw : OneBounded w)
    {η D : ℝ} (hη : 0≤η) (hD : 0≤D)
    (hbase : ∀g : ℕ→ℂ,OneBounded g → Multiplicative g → UniformlyNonpretentious g → WindowBound g η D) :
    WindowBound (fun n=>f n*w (n%q)) ((2:ℝ)^(7*m+16)*η) D := by
  let t : ℝ := (2:ℝ)^(2*m+16)*η
  have ht : 0≤t := by dsimp [t]; positivity
  have hsmall (b : ℕ) : WindowBound
      (fun n=>w b*(f n*(if n ≡ b [MOD q] then (1:ℂ) else 0))) t D := by
    have hc := primeFactors_card_le_five_mul (Nat.gcd_pos_of_pos_right b hq)
      ((Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)).trans hqm)
    have he : (2:ℝ)^(b.gcd q).primeFactors.card≤(2:ℝ)^(2*m+16) :=
      pow_le_pow_right₀ (by norm_num) hc
    have hbudget : (2:ℝ)^(b.gcd q).primeFactors.card*η≤t :=
      mul_le_mul_of_nonneg_right he hη
    have hr := windowBound_mono hD hbudget (residue_bound_from_NP hf hm hNP hq b hη hD hbase)
    exact windowBound_mono hD (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw b) ht)
      (windowBound_const_mul (w b) hr)
  have hs := windowBound_finsetSum (range q)
    (fun b n=>w b*(f n*(if n ≡ b [MOD q] then (1:ℂ) else 0))) (fun _=>t) D
    (fun b _=>hsmall b)
  have he : (∑_b∈range q,t)≤(2:ℝ)^(7*m+16)*η := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    have hqr : (q:ℝ)≤(2:ℝ)^(5*m) := by exact_mod_cast hqm
    calc
      _ ≤ (2:ℝ)^(5*m)*t := mul_le_mul_of_nonneg_right hqr ht
      _ = _ := by dsimp [t]; rw [←mul_assoc,←pow_add]; congr 2; omega
  apply windowBound_congr_pos _ (windowBound_mono hD he hs)
  intro n hn
  exact (finite_residue_expansion f w hq n).symm

theorem periodic_physical_power_logarithmic :
    ∃ A c k v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {q : ℕ}, 0<q → q≤2^(5*m) → ∀w : ℕ→ℂ, OneBounded w →
      ∀D : ℝ, 2*sharpLogGate A c k (16*m+v)≤D →
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*w (n%q)) (fun n=>(n:ℝ)) D x‖)
      ≤ (1/2:ℝ)^m*D*X := by
  obtain ⟨A,c,k,v,hP⟩ := dyadic_physical_power_logarithmic
  refine ⟨A,c,k,40+v,?_⟩
  intro m f hf hm hNP q hq hqm w hw D hD
  let η : ℝ := (1/2:ℝ)^(8*m+20)
  have hη : 0≤η := by dsimp [η]; positivity
  have hDp : 0<D := by
    have ht := sharpLogGate_pos A c k (16*m+(40+v))
    linarith only [ht,hD]
  have hbase (g : ℕ→ℂ) (hg : OneBounded g) (hgm : Multiplicative g)
      (hgn : UniformlyNonpretentious g) : WindowBound g η D := by
    have he : characterModulation g (1:DirichletCharacter ℂ 1)=g := by
      funext n
      have hn : (n:ZMod 1)=1 := Subsingleton.elim _ _
      simp [characterModulation,hn]
    have hgate : 2*sharpLogGate A c k (2*(8*m+20)+v)≤D := by
      convert hD using 1
      congr 2
      omega
    have hL := hP (8*m+20) hg hgm hgn (by decide : 0<(1:ℕ)) (1:DirichletCharacter ℂ 1) D hgate
    filter_upwards [hL] with X hLX
    simpa only [he] using hLX.le
  have hs := periodic_bound_from_NP hf hm hNP hq hqm w hw hη hDp.le hbase
  have hbudget : (2:ℝ)^(7*m+16)*η≤(1/2:ℝ)^m := by
    have hp : (2:ℝ)^(7*m+16)*(1/2:ℝ)^(7*m+16)=1 := by rw [←mul_pow]; norm_num
    dsimp [η]
    rw [show 8*m+20=(7*m+16)+(m+4) by omega,
      pow_add (1/2:ℝ) (7*m+16) (m+4),←mul_assoc,hp,one_mul,pow_add]
    norm_num only [show (1/2:ℝ)^4=1/16 by norm_num]
    nlinarith only [show 0≤(1/2:ℝ)^m by positivity]
  exact windowBound_mono hDp.le hbudget hs

end OrdinaryMellinModulus

end

end OAI
