import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ErrorSampleConstant
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RationalPrimeBlockBudget
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BlockDiagonalBound

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

namespace OrdinaryRationalWidth
open OrdinaryCorrelations OrdinaryCorrelations.SourcePrimeFactor OrdinaryAdditiveBilinear
open OrdinaryNarrowGrid Finset Filter

noncomputable def fixedBudget (P S : Finset ℕ) (D A K q : ℕ) : ℝ :=
  ((A:ℝ)⁻¹*(2/(∑p∈P,(p:ℝ)⁻¹)^2))*
    ((A:ℝ)⁻¹*S.card*(K/q+1:ℕ)+(S.card:ℝ)^2*(q:ℝ)*(4*(A:ℝ)⁻¹*K/D))

lemma rational_fixed_limit (P S : Finset ℕ) (D A K q : ℕ) :
    Tendsto (fun X : ℕ=>normalizedRationalPrimeBlockBudget P S D X A K q)
      atTop (nhds (fixedBudget P S D A K q)) := by
  have ht : Tendsto (fun X : ℕ=>(X:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h₁ := (tendsto_const_nhds (x := (A:ℝ)⁻¹*(2/(∑p∈P,(p:ℝ)⁻¹)^2))).add
    (ht.const_mul (2^(P.card):ℝ))
  have h₂ := (tendsto_const_nhds (x := (A:ℝ)⁻¹*S.card*(K/q+1:ℕ))).add
    (((ht.const_mul 2).add (tendsto_const_nhds (x := 4*(A:ℝ)⁻¹*K/D))).const_mul
      ((S.card:ℝ)^2*(q:ℝ)))
  simpa only [normalizedRationalPrimeBlockBudget,fixedBudget,div_eq_mul_inv,
    mul_zero,add_zero,zero_add] using h₁.mul h₂

lemma bin_card_le (i : ℕ×ℕ) (hi : i.2=1) : (primeBin i).card≤lower i := by
  have hh := Finset.card_le_card (filter_subset Nat.Prime (Finset.Ioc (lower i) (upper i)))
  have he : upper i=lower i+lower i := by simp only [lower,upper,hi]; ring
  simpa only [primeBin,Nat.card_Ioc,he,Nat.add_sub_cancel_left] using hh

lemma fixed_budget_le (P S : Finset ℕ) (D A K q q0 Q E : ℕ)
    (hL : 1≤∑p∈P,(p:ℝ)⁻¹) (hA : 0<A) (hc : S.card≤A)
    (hK : K≤2*A) (hq0 : 0<q0) (hqq0 : q0≤q) (hqQ : q≤Q) (hKE : K≤E) :
    fixedBudget P S D A K q ≤
      ((A:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
        ((A:ℝ)⁻¹*S.card)+4/(q0:ℝ)+8*(Q:ℝ)*E/D := by
  let L : ℝ := ∑p∈P,(p:ℝ)⁻¹
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hAr : (0:ℝ)<A := by exact_mod_cast hA
  have hqr : (0:ℝ)<q0 := by exact_mod_cast hq0
  have hq : 0<q := lt_of_lt_of_le hq0 hqq0
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hC : 2/L^2≤2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
    nlinarith only [hL]
  have hcard : (A:ℝ)⁻¹*S.card≤1 := by
    rw [←div_eq_inv_mul]
    exact (div_le_one hAr).mpr (by exact_mod_cast hc)
  have hdiv : ((K/q:ℕ):ℝ)≤2*(A:ℝ)/(q0:ℝ) := by
    calc
      _ ≤ (K:ℝ)/(q:ℝ) := Nat.cast_div_le
      _ ≤ (2*(A:ℝ))/(q0:ℝ) := by gcongr; exact_mod_cast ‹_›
  have hr : ((A:ℝ)⁻¹*(2/L^2))*((A:ℝ)⁻¹*S.card)*((K/q:ℕ):ℝ)≤4/(q0:ℝ) := by
    calc
      _ ≤ ((A:ℝ)⁻¹*2)*1*(2*(A:ℝ)/(q0:ℝ)) := by gcongr
      _ = _ := by field_simp; ring
  have ho : ((A:ℝ)⁻¹*(2/L^2))*((S.card:ℝ)^2*(q:ℝ)*(4*(A:ℝ)⁻¹*K/D))≤8*(Q:ℝ)*E/D := by
    calc
      _ ≤ ((A:ℝ)⁻¹*2)*((A:ℝ)^2*(Q:ℝ)*(4*(A:ℝ)⁻¹*E/D)) := by
        gcongr
      _ = _ := by field_simp; ring
  have hd : ((A:ℝ)⁻¹*(2/L^2))*((A:ℝ)⁻¹*S.card)≤
      ((A:ℝ)⁻¹*(4/L^2+4/L))*((A:ℝ)⁻¹*S.card) := by
    gcongr
    have h2 : 0≤2/L^2 := by positivity
    have h4 : 0≤4/L := by positivity
    have he : 4/L^2=2*(2/L^2) := by ring
    rw [he]
    linarith
  have he : fixedBudget P S D A K q=
      ((A:ℝ)⁻¹*(2/L^2))*((A:ℝ)⁻¹*S.card)+
      ((A:ℝ)⁻¹*(2/L^2))*((A:ℝ)⁻¹*S.card)*((K/q:ℕ):ℝ)+
      ((A:ℝ)⁻¹*(2/L^2))*((S.card:ℝ)^2*(q:ℝ)*(4*(A:ℝ)⁻¹*K/D)) := by
    simp only [fixedBudget,L,Nat.cast_add,Nat.cast_one]
    ring
  rw [he]
  change _≤((A:ℝ)⁻¹*(4/L^2+4/L))*((A:ℝ)⁻¹*S.card)+4/(q0:ℝ)+8*(Q:ℝ)*E/D
  linarith

lemma sqrt_subadd (a b : ℝ) : Real.sqrt (a+b)≤Real.sqrt a+Real.sqrt b := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),?_⟩
  have ha : a≤(Real.sqrt a)^2 := by rw [Real.sq_sqrt']; exact le_max_left _ _
  have hb : b≤(Real.sqrt b)^2 := by rw [Real.sq_sqrt']; exact le_max_left _ _
  nlinarith only [ha,hb,mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem grid_fixed_budget_bound (P : Finset ℕ) (r R D q q0 Q : ℕ)
    (hL : 1≤∑p∈P,(p:ℝ)⁻¹) (hq0 : 0<q0) (hqq0 : q0≤q) (hqQ : q≤Q) :
    (∑i∈grid 1 r R,Real.sqrt (fixedBudget P (primeBin i) D (lower i) (upper i) q))≤
      12*(3/4:ℝ)^r+R*(Real.sqrt (4/(q0:ℝ))+Real.sqrt (8*(Q:ℝ)*(2:ℝ)^(r+R)/D)) := by
  have hc : (grid 1 r R).card=R := by simp [grid]
  calc
    _ ≤ ∑i∈grid 1 r R,(Real.sqrt
        (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
          ((lower i:ℝ)⁻¹*(primeBin i).card))+
        (Real.sqrt (4/(q0:ℝ))+Real.sqrt (8*(Q:ℝ)*(2:ℝ)^(r+R)/D))) := by
      apply sum_le_sum
      intro i hi
      have hi2 : i.2=1 := by have hh:=mem_Ico.mp (mem_product.mp hi).2; omega
      have hb := fixed_budget_le P (primeBin i) D (lower i) (upper i) q q0 Q (2^(r+R))
        hL (grid_lower_pos 1 r R (by norm_num) hi) (bin_card_le i hi2)
        (upper_le_two_lower 1 r R (by norm_num) hi) hq0 hqq0 hqQ
        (by simpa using upper_le_endpoint 1 r R hi)
      push_cast at hb
      have hs1 := sqrt_subadd
        (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
          ((lower i:ℝ)⁻¹*(primeBin i).card)) (4/(q0:ℝ))
      have hs2 := sqrt_subadd
        (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
          ((lower i:ℝ)⁻¹*(primeBin i).card)+4/(q0:ℝ))
        (8*(Q:ℝ)*(2:ℝ)^(r+R)/D)
      exact (Real.sqrt_le_sqrt hb).trans (by linarith only [hs1,hs2])
    _ = (∑i∈grid 1 r R,Real.sqrt
        (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
          ((lower i:ℝ)⁻¹*(primeBin i).card)))+
        R*(Real.sqrt (4/(q0:ℝ))+Real.sqrt (8*(Q:ℝ)*(2:ℝ)^(r+R)/D)) := by
      rw [sum_add_distrib,Finset.sum_const,hc,nsmul_eq_mul]
    _ ≤ _ := add_le_add (OrdinaryMinorArcNumerics.grid_one_diagonal_bound P r R hL) le_rfl

noncomputable def packetBudget (r R D X q : ℕ) : ℝ :=
  let P := primeWindow 1 r R
  Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card/(X:ℝ)+
    (∑i∈grid 1 r R,Real.sqrt (normalizedRationalPrimeBlockBudget P (primeBin i) D X (lower i) (upper i) q))+
    2*(∑p∈P,(p:ℝ)⁻¹^2)+P.card/(X:ℝ)
noncomputable def packetFixed (r R D q : ℕ) : ℝ :=
  let P := primeWindow 1 r R
  Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+
    (∑i∈grid 1 r R,Real.sqrt (fixedBudget P (primeBin i) D (lower i) (upper i) q))+
    2*(∑p∈P,(p:ℝ)⁻¹^2)

lemma packet_limit (r R D q : ℕ) :
    Tendsto (fun X : ℕ=>packetBudget r R D X q) atTop (nhds (packetFixed r R D q)) := by
  have ht : Tendsto (fun X : ℕ=>(X:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := tendsto_finsetSum (grid 1 r R) (fun i hi=>
    Real.continuous_sqrt.continuousAt.tendsto.comp
      (rational_fixed_limit (primeWindow 1 r R) (primeBin i) D (lower i) (upper i) q))
  have hh := (((((tendsto_const_nhds (x := Real.exp (-(∑p∈primeWindow 1 r R,(p:ℝ)⁻¹)))).add (ht.const_mul (2^((primeWindow 1 r R).card):ℝ))).add hs).add
    (tendsto_const_nhds (x := 2*(∑p∈primeWindow 1 r R,(p:ℝ)⁻¹^2)))).add (ht.const_mul ((primeWindow 1 r R).card:ℝ)))
  simpa only [packetBudget,packetFixed,div_eq_mul_inv,mul_zero,add_zero,Function.comp_def] using hh

theorem minor_arc_explicit_width (r R D q0 Q : ℕ) (hD : 0<D) (hq0 : 0<q0)
    (hL : 1≤∑p∈primeWindow 1 r R,(p:ℝ)⁻¹)
    {f : ℕ→ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ U : ℕ in atTop, ∀q : ℕ, q0≤q → q≤Q →
      ∀a : ℤ, Int.gcd a q=1 → ∀α : ℝ,
      |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*(2:ℝ)^(r+R)) →
      (∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖) ≤
        (Real.exp (-(∑p∈primeWindow 1 r R,(p:ℝ)⁻¹))+
          12*(3/4:ℝ)^r+2/(2:ℝ)^r+
          R*(Real.sqrt (4/(q0:ℝ))+Real.sqrt (8*(Q:ℝ)*(2:ℝ)^(r+R)/D))+ε)*D*(U+D) := by
  let P := primeWindow 1 r R
  let C := Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+
          12*(3/4:ℝ)^r+2/(2:ℝ)^r+
          R*(Real.sqrt (4/(q0:ℝ))+Real.sqrt (8*(Q:ℝ)*(2:ℝ)^(r+R)/D))
  have hfix (q : ℕ) (hq : q∈Finset.Icc q0 Q) : packetFixed r R D q≤C := by
    have hs := grid_fixed_budget_bound P r R D q q0 Q hL hq0 (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
    have hp := OrdinaryChainScales.prime_window_square_sum 1 r R (by norm_num)
    norm_num only [one_mul,Nat.cast_pow,Nat.cast_ofNat] at hp
    have hp2 : 2*(∑p∈primeWindow 1 r R,(p:ℝ)⁻¹^2)≤2/(2:ℝ)^r := by
      calc
        _ ≤ 2*(1/(2:ℝ)^r) := mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = _ := by ring
    dsimp only [packetFixed,C,P] at hs ⊢
    linarith only [hs,hp2]
  have hall : ∀ᶠ U : ℕ in atTop,∀q∈Finset.Icc q0 Q,packetBudget r R D (U+D) q≤C+ε := by
    apply (eventually_all_finset (Finset.Icc q0 Q)).mpr
    intro q hq
    have ht := (packet_limit r R D q).comp (tendsto_add_atTop_nat D)
    exact ((tendsto_order.mp ht).2 _ (lt_of_le_of_lt (hfix q hq) (by linarith))).mono
      (fun U hU=>hU.le)
  filter_upwards [hall,eventually_ge_atTop (2^(r+R))] with U hU hUE
  intro q hq0q hqQ a haq α hα
  have hq : 0<q := lt_of_lt_of_le hq0 hq0q
  have hX : 0<U+D := by omega
  have hXr : (0:ℝ)<(U+D:ℕ) := by exact_mod_cast hX
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hP : ∀p∈P,Nat.Prime p := fun p hp=>(mem_filter.mp hp).2
  have hAi (i : ℕ×ℕ) (hi : i∈grid 1 r R) : 0<lower i := grid_lower_pos 1 r R (by norm_num) hi
  have hKi (i : ℕ×ℕ) (hi : i∈grid 1 r R) : 0<upper i := (hAi i hi).trans_le (lower_le_upper i)
  have hEi (i : ℕ×ℕ) (hi : i∈grid 1 r R) : upper i≤2^(r+R) := by
    simpa only [one_mul] using upper_le_endpoint 1 r R hi
  have hNi (i : ℕ×ℕ) (hi : i∈grid 1 r R) : 0<(U+D)/lower i :=
    Nat.div_pos (by have hh:=(lower_le_upper i).trans (hEi i hi); omega) (hAi i hi)
  have hphase (i : ℕ×ℕ) (hi : i∈grid 1 r R) : |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*upper i) := by
    apply hα.trans
    have hp : (0:ℝ)<upper i := by exact_mod_cast hKi i hi
    have hqr : (0:ℝ)<q := by exact_mod_cast hq
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact_mod_cast hEi i hi
  have hs := actual_short_near_rational_blocks_normalized (grid 1 r R) primeBin P hP
    (prime_window_bins 1 r R) (prime_bins_disjoint 1 r R (by norm_num)) f hf hm D U hX lower upper α a q hq haq
    hAi hNi (fun i hi p hp=>(mem_Ioc.mp (mem_filter.mp hp).1).1.le)
    (fun i hi p hp=>(mem_Ioc.mp (mem_filter.mp hp).1).2)
    (lt_of_lt_of_le (by norm_num) hL) hKi hphase
  have hb := hs.trans (hU q (Finset.mem_Icc.mpr ⟨hq0q,hqQ⟩))
  have ht := (div_le_iff₀ hXr).mp hb
  have hh := mul_le_mul_of_nonneg_left ht hDr.le
  simp only [←mul_assoc,mul_inv_cancel₀ hDr.ne',one_mul] at hh
  change _≤(C+ε)*(D:ℝ)*((U:ℝ)+D)
  have he : (D:ℝ)*(C+ε)*((U+D:ℕ):ℝ)=(C+ε)*(D:ℝ)*((U:ℝ)+D) := by push_cast; ring
  rw [he] at hh
  exact hh

end OrdinaryRationalWidth

end

end OAI
