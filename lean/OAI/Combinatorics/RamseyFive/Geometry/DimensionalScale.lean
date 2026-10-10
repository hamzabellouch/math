import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventuallyHighPolyCost
import OAI.Combinatorics.RamseyFive.Geometry.MomentOrder
import OAI.Combinatorics.RamseyFive.Entropy.LowBudgetPoly

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open scoped BigOperators

noncomputable def dimensionalScale (q d : ℕ) (n : ℝ) : ℝ := (q:ℝ)^d/n

lemma pencil_alphabet_exp {q k : ℕ} {σ : ℝ} (hk : 1≤k) (hσ : 0≤σ)
    (hq : (q:ℝ)=Real.exp σ) : (pencilAlphabet q k:ℝ)≤(k:ℝ)*Real.exp (((k:ℝ)-1)*σ) := by
  have hq1 : 1≤q := by exact_mod_cast (hq▸Real.one_le_exp_iff.mpr hσ)
  have hh := pencilAlphabet_le (k:=k) hq1
  rw [hq,←Real.exp_nat_mul,Nat.cast_sub hk,Nat.cast_one] at hh
  exact hh

lemma dimensional_budget_ratios {q d : ℕ} {σ n : ℝ} (hd : 2≤d) (hdhi : d≤4)
    (hσ : 20≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) :
    1≤dimensionalScale q d n ∧
    (pencilAlphabet q d:ℝ)/(dimensionalScale q d n*(Real.exp (σ/5))^8)≤40 ∧
    (pencilAlphabet q (d-2):ℝ)*Real.exp (σ/5)/dimensionalScale q d n≤20 ∧
    (pencilAlphabet q d:ℝ)/(dimensionalScale q d n)^2≤400 := by
  let B := dimensionalScale q d n
  let a : ℝ := ((d:ℝ)-1)*σ/2
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hdRhi : (d:ℝ)≤4 := by exact_mod_cast hdhi
  have hσ0 : 0≤σ := by linarith
  have hlo : Real.exp a/10≤B := by
    unfold B dimensionalScale
    apply (le_div_iff₀ hn).mpr
    calc
      _ ≤ (Real.exp a/10)*(10*Real.exp (((d:ℝ)+1)*σ/2)) :=
        mul_le_mul_of_nonneg_left hnhi (by positivity)
      _ = Real.exp ((d:ℝ)*σ) := by
        rw [show (Real.exp a/10)*(10*Real.exp (((d:ℝ)+1)*σ/2))=
          Real.exp a*Real.exp (((d:ℝ)+1)*σ/2) by ring,←Real.exp_add]
        congr 1
        dsimp [a]
        ring
      _ = (q:ℝ)^d := by rw [hq,←Real.exp_nat_mul]
  have ha : 10≤a := by dsimp [a];nlinarith
  have hB1 : 1≤B := by have hh := Real.add_one_le_exp a;linarith
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hQ : (pencilAlphabet q d:ℝ)≤4*Real.exp (((d:ℝ)-1)*σ) :=
    (pencil_alphabet_exp (by omega) hσ0 hq).trans
      (mul_le_mul_of_nonneg_right hdRhi (Real.exp_nonneg _))
  have hb8 : (Real.exp (σ/5))^8=Real.exp (8*σ/5) := by
    rw [←Real.exp_nat_mul];congr 1;norm_num;ring
  refine ⟨hB1,?_,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos hB0 (pow_pos (Real.exp_pos _) _))).mpr
    calc
      _ ≤ 4*Real.exp (((d:ℝ)-1)*σ) := hQ
      _ ≤ 4*Real.exp (a+8*σ/5) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [a]
        nlinarith
      _ = 40*((Real.exp a/10)*(Real.exp (σ/5))^8) := by rw [hb8,Real.exp_add];ring
      _ ≤ 40*(B*(Real.exp (σ/5))^8) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlo (by positivity)) (by norm_num)
  · by_cases hd2 : d=2
    · subst d
      norm_num [pencilAlphabet]
    have hdk : 1≤d-2 := by omega
    have hN : (pencilAlphabet q (d-2):ℝ)≤2*Real.exp (((d:ℝ)-3)*σ) := by
      have hh := pencil_alphabet_exp (k:=d-2) hdk hσ0 hq
      rw [Nat.cast_sub hd,Nat.cast_ofNat] at hh
      have he : (d:ℝ)-2-1=(d:ℝ)-3 := by ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
    apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (2*Real.exp (((d:ℝ)-3)*σ))*Real.exp (σ/5) :=
        mul_le_mul_of_nonneg_right hN (Real.exp_nonneg _)
      _ = 2*Real.exp (((d:ℝ)-3)*σ+σ/5) := by rw [mul_assoc,←Real.exp_add]
      _ ≤ 2*Real.exp a := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [a]
        nlinarith
      _ = 20*(Real.exp a/10) := by ring
      _ ≤ 20*B := mul_le_mul_of_nonneg_left hlo (by norm_num)
  · apply (div_le_iff₀ (sq_pos_of_pos hB0)).mpr
    calc
      _ ≤ 4*Real.exp (((d:ℝ)-1)*σ) := hQ
      _ = 400*(Real.exp a/10)^2 := by
        rw [div_pow,←Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2:ℝ)*a=((d:ℝ)-1)*σ by dsimp [a];ring]
        ring
      _ ≤ 400*B^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo 2) (by norm_num)

lemma low_one_anchor_ratio {q d : ℕ} {σ n P : ℝ} (hd : 2≤d) (hdhi : d≤4)
    (hσ : 0≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hsmall : n≤(q:ℝ)^2*Real.exp (P/10000)) :
    (pencilAlphabet q (d-1):ℝ)/dimensionalScale q d n≤4*Real.exp (P/10000) := by
  have hq0 : 0<(q:ℝ) := hq▸Real.exp_pos _
  have hdR : (d:ℝ)≤4 := by exact_mod_cast hdhi
  have hB : 0<dimensionalScale q d n := div_pos (pow_pos hq0 _) hn
  have hN : (pencilAlphabet q (d-1):ℝ)≤4*(q:ℝ)^(d-2) := by
    have hh := pencilAlphabet_le (k:=d-1) (show 1≤q by exact_mod_cast (hq▸Real.one_le_exp_iff.mpr hσ))
    rw [Nat.sub_sub] at hh
    norm_num only [Nat.reduceAdd] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (by rw [Nat.cast_sub (by omega),Nat.cast_one];linarith) (by positivity)
  apply (div_le_iff₀ hB).mpr
  unfold dimensionalScale
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (4*(q:ℝ)^(d-2))*((q:ℝ)^2*Real.exp (P/10000)) :=
      mul_le_mul hN hsmall hn.le (by positivity)
    _ = (4*Real.exp (P/10000))*(q:ℝ)^d := by
      rw [show (q:ℝ)^d=(q:ℝ)^(d-2)*(q:ℝ)^2 by rw [←pow_add];congr 1;omega]
      ring

end

open Filter ParameterHierarchy
open scoped Topology

lemma dimensionalScale_oriented_lower {q d : ℕ} {σ n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) :
    Real.exp (((d:ℝ)-1)*σ/2)/10≤dimensionalScale q d n := by
  unfold dimensionalScale
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (Real.exp (((d:ℝ)-1)*σ/2)/10)*(10*Real.exp (((d:ℝ)+1)*σ/2)) :=
      mul_le_mul_of_nonneg_left hnhi (by positivity)
    _ = Real.exp ((d:ℝ)*σ) := by
      rw [show (Real.exp (((d:ℝ)-1)*σ/2)/10)*(10*Real.exp (((d:ℝ)+1)*σ/2))=
        Real.exp (((d:ℝ)-1)*σ/2)*Real.exp (((d:ℝ)+1)*σ/2) by ring,←Real.exp_add]
      congr 1
      ring
    _ = (q:ℝ)^d := by rw [hq,←Real.exp_nat_mul]

lemma dimensional_strong_scale {q d : ℕ} {σ n P : ℝ} (hd : 2≤d)
    (hσ : 100≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) (hP : 1≤P) (hPhi : P≤σ/10) :
    2+dimensionalScale q d n*Real.exp (-3*P)≤dimensionalScale q d n*Real.exp (-P) := by
  let B := dimensionalScale q d n
  have hBlo := dimensionalScale_oriented_lower hq hn hnhi
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hlarge : 4≤B*Real.exp (-P) := by
    have he := Real.add_one_le_exp (((d:ℝ)-1)*σ/2-P)
    have hh : Real.exp (((d:ℝ)-1)*σ/2-P)/10≤B*Real.exp (-P) := by
      calc
        _ = (Real.exp (((d:ℝ)-1)*σ/2)/10)*Real.exp (-P) := by rw [Real.exp_sub,Real.exp_neg];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hBlo (Real.exp_nonneg _)
    nlinarith
  have hE : Real.exp (-2*P)≤1/2 := by
    have he : (2:ℝ)≤Real.exp (2*P) := by linarith [Real.add_one_le_exp (2*P)]
    rw [show -2*P=-(2*P) by ring,Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he)
  have hB : 0≤B := by unfold B dimensionalScale;positivity
  have hterm : B*Real.exp (-3*P)≤(B*Real.exp (-P))/2 := by
    calc
      _ = (B*Real.exp (-P))*Real.exp (-2*P) := by rw [mul_assoc,←Real.exp_add];congr 2;ring
      _ ≤ (B*Real.exp (-P))*(1/2) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  linarith

theorem eventually_low_geometric_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q d m : ℕ) (n D : ℝ) (R : ℕ),
      2≤d → d≤4 → (q:ℝ)=Real.exp σ → 0<n →
      n≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      n≤(q:ℝ)^2*Real.exp (P η σ D R/10000) →
      (m:ℝ)≤Real.exp (3*σ) → Range η σ D R →
      let B := dimensionalScale q d n
      let p := momentOrder σ (P η σ D R)
      let a := dyadFactor m (P η σ D R/100)
      10000≤L η σ D ∧
      40*B*Real.exp (L η σ D/100)+2*((p+1:ℝ)*
        lowMomentBudget (pencilAlphabet q d) (a*B^2) (a*B) B (Real.exp (σ/5))
          (L η σ D) p R (pencilAlphabet q (d-1)) (pencilAlphabet q (d-2)))≤
        B*Real.exp (P η σ D R/5) ∧
      (pencilAlphabet q d:ℝ)+(a*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (P η σ D R/10) ∧
      (p:ℝ)^2≤Real.exp (P η σ D R/10) ∧
      2+B*Real.exp (-3*P η σ D R)≤B*Real.exp (-P η σ D R) := by
  let c : ℝ := 8*2^(200:ℕ)
  have hcost := eventually_low_poly_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hpairs := eventually_high_pair_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hhier := eventually_hierarchy hη hη' 0 (1/10) 10000 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),hcost,hpairs,hhier] with σ hσ hc hp hh
  intro q d m n D R hd hdhi hq hn hnor hlow hm hr
  have hσ1 : 1≤σ := by linarith
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ1 hr
  have ht := hh D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
  have hL : 10000≤L η σ D := ht.1
  have hPσ : P η σ D R≤σ/10 := by simpa only [div_eq_mul_inv,one_mul,mul_comm (10⁻¹:ℝ)] using ht.2.1
  have hL0 : 0<L η σ D := by linarith
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hP1 : 1≤P η σ D R := by unfold P; nlinarith
  let B := dimensionalScale q d n
  let p := momentOrder σ (P η σ D R)
  let a := dyadFactor m (P η σ D R/100)
  obtain ⟨_,hpos,_,_,hps⟩ := momentOrder_bounds hσ1 hP1
  have hrat := dimensional_budget_ratios hd hdhi (by linarith) hq hn hnor
  have hB : 0<B := lt_of_lt_of_le zero_lt_one hrat.1
  have hB1 : 1≤B := hrat.1
  have ha : 0≤a := by dsimp [a,dyadFactor];positivity
  have has : a≤c*σ*Real.exp (P η σ D R/50) := dyadFactor_exp_bound hσ1 hm
  have hs := low_one_anchor_ratio hd hdhi (by linarith) hq hn hlow
  have hc' := hc D R p a ((pencilAlphabet q (d-1):ℝ)/B) hr
    (Nat.cast_nonneg _) hps ha has hs
  have hp' := hp D R p a hr (Nat.cast_nonneg _) hps ha has
  have hbudget := lowMomentBudget_le_poly (pencilAlphabet q d) a
    ((pencilAlphabet q (d-1):ℝ)/B) B (Real.exp (σ/5)) (L η σ D) p R
    (pencilAlphabet q (d-1)) (pencilAlphabet q (d-2)) hB1 (Real.exp_pos _) ha hL0.le
    hrat.2.1 hrat.2.2.1 hrat.2.2.2 (le_refl _)
  have hPL : (R:ℝ)*L η σ D=P η σ D R := by unfold P;ring
  rw [hPL] at hbudget
  have hsingleton : 40*Real.exp (L η σ D/100)≤Real.exp (P η σ D R/50) := by
    have h40 : (40:ℝ)≤Real.exp (L η σ D/100) := by linarith [Real.add_one_le_exp (L η σ D/100)]
    calc
      _ ≤ Real.exp (L η σ D/100)*Real.exp (L η σ D/100) := mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _)
      _ = Real.exp (L η σ D/50) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold P;nlinarith)
  refine ⟨hL,?_,?_,hp'.2,dimensional_strong_scale hd hσ hq hn hnor hP1 hPσ⟩
  · calc
      _ ≤ B*Real.exp (P η σ D R/50)+2*((p+1:ℝ)*(B*lowBudgetPoly a
          ((pencilAlphabet q (d-1):ℝ)/B) p (P η σ D R))) := by
        apply add_le_add
        · nlinarith only [mul_le_mul_of_nonneg_left hsingleton hB.le]
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (by positivity)) (by norm_num)
      _ = B*(Real.exp (P η σ D R/50)+2*(p+1)*lowBudgetPoly a
          ((pencilAlphabet q (d-1):ℝ)/B) p (P η σ D R)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' hB.le
  · have htpos : 0<1/(100*(p:ℝ)) := by positivity
    have hQ : (pencilAlphabet q d:ℝ)≤400*B^2 := (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2
    calc
      _ = (pencilAlphabet q d:ℝ)+B^2*(a*(100*(p:ℝ))^200) := by rw [div_pow,one_pow];field_simp;ring
      _ ≤ 400*B^2+B^2*(a*(100*(p:ℝ))^200) := add_le_add hQ (le_refl _)
      _ = B^2*(400+a*(100*(p:ℝ))^200) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg _)

end SharpRamseyFive.ScoreGeometry

end

end OAI
