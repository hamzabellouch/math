import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.ProjectiveHighCapturedMoment
import OAI.Combinatorics.RamseyFive.Geometry.PencilLineSum
import OAI.Combinatorics.RamseyFive.Geometry.PointStrength
import OAI.Combinatorics.RamseyFive.Entropy.EventuallyHighPolyCost
import OAI.Combinatorics.RamseyFive.Geometry.MomentOrder
import OAI.Combinatorics.RamseyFive.Geometry.GeometryScaleOrientedLower

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open scoped BigOperators

lemma pencil_high_budget_ratios {q : ℕ} {σ n : ℝ} (hσ : 10≤σ)
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2)) :
    1≤geometryScale q n ∧
    (pencilAlphabet q 4:ℝ)/(geometryScale q n*(Real.exp (σ/5))^8)≤40 ∧
    (pencilAlphabet q 2:ℝ)*Real.exp (σ/5)/geometryScale q n≤20 ∧
    (pencilAlphabet q 4:ℝ)/(geometryScale q n)^2≤400 := by
  let B := geometryScale q n
  have hσ0 : 0≤σ := by linarith
  have hq1 : 1≤q := by
    have hh := hq▸Real.one_le_exp_iff.mpr hσ0
    exact_mod_cast hh
  have hBlo : Real.exp (3*σ/2)/10≤B := by
    unfold B geometryScale
    apply (le_div_iff₀ hn).mpr
    calc
      _ ≤ (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2)) :=
        mul_le_mul_of_nonneg_left hnhi (by positivity)
      _ = Real.exp (4*σ) := by
        rw [show (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2))=Real.exp (3*σ/2)*Real.exp (5*σ/2) by ring]
        rw [←Real.exp_add]
        congr 1
        ring
      _ = (q:ℝ)^4 := by rw [hq,←Real.exp_nat_mul]; norm_num
  have hB1 : 1≤B := by
    have he := Real.add_one_le_exp (3*σ/2)
    linarith
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hQ : (pencilAlphabet q 4:ℝ)≤4*Real.exp (3*σ) := by
    have hh := pencilAlphabet_le (k:=4) hq1
    norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hh
    rw [hq,←Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hN : (pencilAlphabet q 2:ℝ)≤2*Real.exp σ := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,hq] using pencilAlphabet_le (k:=2) hq1
  have hb8 : (Real.exp (σ/5))^8=Real.exp (8*σ/5) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  refine ⟨hB1,?_,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos hB0 (pow_pos (Real.exp_pos _) _))).mpr
    calc
      _ ≤ 4*Real.exp (3*σ) := hQ
      _ ≤ 4*Real.exp (3*σ/2+8*σ/5) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = 40*((Real.exp (3*σ/2)/10)*(Real.exp (σ/5))^8) := by
        rw [hb8,Real.exp_add]
        ring
      _ ≤ 40*(B*(Real.exp (σ/5))^8) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBlo (by positivity)) (by norm_num)
  · apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (2*Real.exp σ)*Real.exp (σ/5) := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg _)
      _ = 2*Real.exp (σ+σ/5) := by rw [mul_assoc,←Real.exp_add]
      _ ≤ 2*Real.exp (3*σ/2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = 20*(Real.exp (3*σ/2)/10) := by ring
      _ ≤ 20*B := mul_le_mul_of_nonneg_left hBlo (by norm_num)
  · apply (div_le_iff₀ (sq_pos_of_pos hB0)).mpr
    calc
      _ ≤ 4*Real.exp (3*σ) := hQ
      _ = 400*(Real.exp (3*σ/2)/10)^2 := by
        rw [div_pow,←Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2:ℝ)*(3*σ/2)=3*σ by ring]
        ring
      _ ≤ 400*B^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBlo 2) (by norm_num)

end

section
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_high_geometric_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q m : ℕ) (n D : ℝ) (R : ℕ),
      (q:ℝ)=Real.exp σ → 0<n →
      n≤10*Real.exp (5*σ/2) →
      (m:ℝ)≤Real.exp (3*σ) → Range η σ D R →
      let B := geometryScale q n
      let p := momentOrder σ (P η σ D R)
      let a := dyadFactor m (P η σ D R/100)
      10000≤L η σ D ∧
      (40*B*Real.exp (L η σ D/100)+B)+2*((p+1:ℝ)*
        highMomentBudget (pencilAlphabet q 4) (a*B^2) (a*B) B (Real.exp (σ/5))
          (L η σ D) p R (pencilAlphabet q 2))≤
        B*Real.exp (P η σ D R/5) ∧
      (pencilAlphabet q 4:ℝ)+(a*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (P η σ D R/10) ∧
      (p:ℝ)^2≤Real.exp (P η σ D R/10) ∧
      2≤B*Real.exp (-P η σ D R) ∧
      16*((q:ℝ)+1)≤(B*Real.exp (-P η σ D R))*(1/(100*(p:ℝ)))^2 := by
  let c : ℝ := 8*2^(200:ℕ)
  have hcost := eventually_high_poly_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hpairs := eventually_high_pair_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hhier := eventually_hierarchy hη hη' 0 (1/10) 10000 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (20000000:ℝ),hcost,hpairs,hhier] with σ hσ hc hp hh
  intro q m n D R hq hn hnor hm hr
  have hσ1 : 1≤σ := by linarith
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ1 hr
  have ht := hh D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
  have hL : 10000≤L η σ D := ht.1
  have hPσ : P η σ D R≤σ/10 := by simpa only [div_eq_mul_inv,one_mul,mul_comm (10⁻¹:ℝ)] using ht.2.1
  have hL0 : 0<L η σ D := by linarith
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hP1 : 1≤P η σ D R := by unfold P; nlinarith
  let B := geometryScale q n
  let p := momentOrder σ (P η σ D R)
  let a := dyadFactor m (P η σ D R/100)
  obtain ⟨_,hpos,_,_,hps⟩ := momentOrder_bounds hσ1 hP1
  have hrat := pencil_high_budget_ratios (by linarith) hq hn hnor
  have hB : 0<B := lt_of_lt_of_le zero_lt_one hrat.1
  have hB1 : 1≤B := hrat.1
  have ha : 0≤a := by dsimp [a,dyadFactor];positivity
  have has : a≤c*σ*Real.exp (P η σ D R/50) := dyadFactor_exp_bound hσ1 hm
  have hc' := hc D R p a hr
    (Nat.cast_nonneg _) hps ha has
  have hp' := hp D R p a hr (Nat.cast_nonneg _) hps ha has
  have hbudget := highMomentBudget_le_poly (pencilAlphabet q 4) a B (Real.exp (σ/5))
    (L η σ D) p R (pencilAlphabet q 2) hB1 (Real.exp_pos _) ha hL0.le
    hrat.2.1 hrat.2.2.1 hrat.2.2.2
  have hPL : (R:ℝ)*L η σ D=P η σ D R := by unfold P;ring
  rw [hPL] at hbudget
  have hsingleton : (40*Real.exp (L η σ D/100)+1)≤Real.exp (P η σ D R/50) := by
    have h40 : (41:ℝ)≤Real.exp (L η σ D/100) := by linarith [Real.add_one_le_exp (L η σ D/100)]
    calc
      _ ≤ 41*Real.exp (L η σ D/100) := by
        have he := Real.one_le_exp_iff.mpr (by positivity : 0≤L η σ D/100)
        linarith
      _ ≤ Real.exp (L η σ D/100)*Real.exp (L η σ D/100) := mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _)
      _ = Real.exp (L η σ D/50) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold P;nlinarith)
  refine ⟨hL,?_,?_,hp'.2,high_strong_scale hσ hq hn hnor hPσ (Nat.cast_pos.mpr hpos) hp'.2⟩
  · calc
      _ ≤ B*Real.exp (P η σ D R/50)+2*((p+1:ℝ)*(B*highBudgetPoly a p (P η σ D R))) := by
        apply add_le_add
        · nlinarith only [mul_le_mul_of_nonneg_left hsingleton hB.le]
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (by positivity)) (by norm_num)
      _ = B*(Real.exp (P η σ D R/50)+2*(p+1)*highBudgetPoly a p (P η σ D R)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' hB.le
  · have htpos : 0<1/(100*(p:ℝ)) := by positivity
    have hQ : (pencilAlphabet q 4:ℝ)≤400*B^2 := (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2
    calc
      _ = (pencilAlphabet q 4:ℝ)+B^2*(a*(100*(p:ℝ))^200) := by rw [div_pow,one_pow];field_simp;ring
      _ ≤ 400*B^2+B^2*(a*(100*(p:ℝ))^200) := add_le_add hQ (le_refl _)
      _ = B^2*(400+a*(100*(p:ℝ))^200) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg _)

theorem eventually_high_local_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q m : ℕ) (n D : ℝ) (R : ℕ),
      (q:ℝ)=Real.exp σ → 0<n → (m:ℝ)≤Real.exp (3*σ) →
      Range η σ D R → (q:ℝ)^2*Real.exp (P η σ D R/10000)≤n →
      ((q:ℝ)/n*((q:ℝ)+1)≤2) ∧
      (208*2^198:ℝ)≤Real.exp (2*(P η σ D R/100)) ∧
      (pencilAlphabet q 3:ℝ)*(P η σ D R)^5000*
        (((q:ℝ)/n*((q:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 m:ℝ)+1)*
            ((q:ℝ)^4/n^2*Real.exp (P η σ D R/100))))≤geometryScale q n := by
  have ht := eventually_local_trunc_scalar hη hη'
  have hs := eventually_hierarchy hη hη' 0 1
    (max 10000 (50*Real.log (208*2^(198:ℕ)))) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht,hs] with σ hσ ht hs
  intro q m n D R hq hn hm hr hnlo
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ hr
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hL : max 10000 (50*Real.log (208*2^(198:ℕ)))≤L η σ D :=
    (hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)).1
  have hL0 : 0≤L η σ D := by linarith [le_max_left (10000:ℝ) (50*Real.log (208*2^(198:ℕ)))]
  have hLP : L η σ D≤P η σ D R := by unfold P;nlinarith
  have hP0 : 0≤P η σ D R := hL0.trans hLP
  let g := Real.log n-2*σ
  have hnexp : n=Real.exp (2*σ+g) := by
    rw [show 2*σ+g=Real.log n by dsimp [g];ring,Real.exp_log hn]
  have hq2 : (q:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul];norm_num
  have hg : P η σ D R/10000≤g := by
    rw [hq2,hnexp,←Real.exp_add,Real.exp_le_exp] at hnlo
    linarith
  have hg0 : 0≤g := (by positivity : 0≤P η σ D R/10000).trans hg
  have hq1 : 1≤(q:ℝ) := by rw [hq];exact Real.one_le_exp_iff.mpr (by linarith)
  have heq : (q:ℝ)^2/n=Real.exp (-g) := by
    rw [hq2,hnexp,←Real.exp_sub]
    congr 1
    ring
  have hM : 0≤(q:ℝ)/n*((q:ℝ)+1) := by positivity
  have hMhi : (q:ℝ)/n*((q:ℝ)+1)≤2*Real.exp (-g) := by
    rw [←heq]
    calc
      _ = ((q:ℝ)*((q:ℝ)+1))/n := by ring
      _ ≤ (2*(q:ℝ)^2)/n := div_le_div_of_nonneg_right (by nlinarith [hq1]) hn.le
      _ = _ := by ring
  have hMmax : (q:ℝ)/n*((q:ℝ)+1)≤2 := by
    exact hMhi.trans (by nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg0)])
  refine ⟨hMmax,?_,?_⟩
  · have hc : (0:ℝ)<208*2^(198:ℕ) := mul_pos (by norm_num) (pow_pos (by norm_num) _)
    apply (Real.log_le_iff_le_exp hc).mp
    have hh := le_max_right (10000:ℝ) (50*Real.log (208*2^(198:ℕ)))
    have hlog : 50*Real.log (208*2^(198:ℕ):ℝ)≤P η σ D R := hh.trans (hL.trans hLP)
    calc
      Real.log (208*2^(198:ℕ):ℝ) = (50*Real.log (208*2^(198:ℕ):ℝ))/50 := by ring
      _ ≤ P η σ D R/50 := div_le_div_of_nonneg_right hlog (by norm_num)
      _ = _ := by ring
  · exact (high_local_radial_numeric hσ hq hnexp hP0 hM
      (hMhi.trans (by linarith [Real.exp_nonneg (-g)])) hm).trans
      (by
        have hB : 0≤geometryScale q n := by unfold geometryScale;positivity
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left (ht D R g hr hg) hB))

end
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open ProjectiveTraining GlobalRadial WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_high_independent {J : Type} [Fintype J]
    (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (R : ℕ) (hR : 2≤R/2)
    (hx : x∉irregular (d:=4) S C ((L:ℝ)/100))
    (χ : ℝ) (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
      x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((((pointStrength S:ℝ)*2^i)/2)) Lines Q
        ((Nat.card K:ℝ)^4/S.card^2*Real.exp χ/(((pointStrength S:ℝ)*2^i)/2)^100)) :
    (∑H:F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (fun e => L*radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) e)
      (pencilLines x F) R 5000 (1-ownFraction S (C a) (C b)) H)≤
      40*scale (K:=K) 4 S.card*Real.exp ((L:ℝ)/100)+
      (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
        (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
            ((Nat.card K:ℝ)^4/S.card^2*Real.exp χ))) := by
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim (by norm_num) S C hS a b c ha hb hc F hF
    (by positivity : 0≤(L:ℝ)/100) hx (hn.trans (by norm_num))
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hpow := radial_high_moment x S (fun _ => C a∪C b) (pointStrength S) hδ S.card χ
    (Nat.cast_pos.mpr hS.card_pos) hmax Lines hLines Q hxQ hgood 5000 (by norm_num)
  exact independent_sum_le x hdim _ _ L F _ _ _ R 5000 hR
    (fun H => (hm H).2.1.trans (by norm_num)) (by simpa only [sq_abs] using hv)
    hpow ((Finset.sum_nonneg fun _ _ => pow_nonneg (NNReal.coe_nonneg _) _).trans hpow)

theorem actual_high_radial_moment {J : Type} [Fintype J]
    (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p)
    (hKR : 200≤R/2) (hh : 0<h) (hsize : h≤(R/2-5000)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=4) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1≤cut)
    (hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hchi : (208*2^198:ℝ)≤Real.exp (2*(((L:ℝ)*R)/100)))
    (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
      x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
        (((pointStrength S:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100)/
          (((pointStrength S:ℝ)*2^i)/2)^100))
    (hPow : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)
    (hlocal : (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
        (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
            ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100))))≤
      geometryScale (Nat.card K) S.card)
    (hcost : (40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
      geometryScale (Nat.card K) S.card)+2*((p+1:ℝ)*
        pencilHighBudget (Nat.card K) (outsideAt x S (C a∪C b)).card S.card
          (((L:ℝ)*R)/100) cut L p R)≤
      geometryScale (Nat.card K) S.card*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hA : 2≤geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1)≤
      (geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
      ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (geometryScale (Nat.card K) S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (own : F→Fin R→Bool) :
    (∫ω,HighMoment.allTrunc R 5000 ω*(∑H:F,scoreTerm (pencilLines x F H)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*
        radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
      (geometryScale (Nat.card K) S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hD := actual_high_independent x hdim S C hS a b c ha hb hc F hF hf hn L R
    (by omega) hx (((L:ℝ)*R)/100) hmax Lines hLines Q hxQ hgood
  have hD' : (∑H:F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (fun e => L*radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) e)
      (pencilLines x F) R 5000 (1-ownFraction S (C a) (C b)) H)≤
      40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
      geometryScale (Nat.card K) S.card := by
    exact hD.trans (add_le_add (by simp [scale,geometryScale]) hlocal)
  apply projective_high_moment_from_pairs x hdim S (fun _ => C a∪C b)
    (pointStrength S) L hδ F (fun H hH => (hF H hH).1) S.card (((L:ℝ)*R)/100)
    cut (1-ownFraction S (C a) (C b)) _ (Nat.cast_pos.mpr hS.card_pos) hcut
    (by unfold geometryScale;positivity) hL (by linarith only [hf]) hcap ?_ hchi
    (fun H => (hm H).2.2.trans (by norm_num)) (fun H => (hm H).1)
    (fun H => (hm H).2.1) Lines hLines Q hxQ hPow hp R h hKR hh hsize herr
    own hD' hcost hp2 hA hscale hstrong hpairScalar
  rw [coe_pointStrength,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos))]
  nlinarith only [Nat.cast_nonneg (α:=ℝ) (Nat.card K)]

end SharpRamseyFive.ScoreGeometry

end OAI
