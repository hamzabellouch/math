import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.High
import OAI.Combinatorics.RamseyFive.Probability.UniformTails

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_high_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (5*σ/2) →
      (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000)≤(S.card:ℝ) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      ∀ (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
        x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
          (((pointStrength S:ℝ)*2^i)/2) Lines Q
          ((Nat.card K:ℝ)^4/S.card^2*Real.exp (P η σ D R/100)/
            (((pointStrength S:ℝ)*2^i)/2)^100)) →
      ((∑z : WeightedPrograms.DistinctPairs F,WeightedPrograms.strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
        dyadFactor (outsideAt x S (C a∪C b)).card (P η σ D R/100)*
          (geometryScale (Nat.card K) S.card)^2) →
      x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 →
      geometryScale (Nat.card K) S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ))+
      ∫ω,1-HighMoment.allTrunc R 5000 ω
        ∂batchMeasure (fun i : Fin R×RadialLine x => L₀*
          radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2) := by
  have hh := eventually_high_geometric_budget hη hη'
  have hl := eventually_high_local_budget hη hη'
  have ho := eventually_moment_orders hη hη'
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),hh,hl,ho,hm] with σ hσ hh hl ho hm
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hShigh hn hf hF hx Lines Q hLines hxQ hgood hPow hstrong ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hcard : ((outsideAt x S (C a∪C b)).card:ℝ)≤Real.exp (3*σ) := by
    have hsub : (outsideAt x S (C a∪C b)).card≤S.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        have hy' : y.val∈S\(C a∪C b) := by simpa [outsideAt] using hy
        exact (Finset.mem_sdiff.mp hy').1
      · intro y hy z hz he
        exact Subtype.ext he
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr hsub
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := by
        exact mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hbudget := hh (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hSn hcard hr
  have hlocal := hl (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hcard hr hShigh
  obtain ⟨heven,hp,hplo,hphi,hps,hKR,hhpos,hhsize,herr⟩ := ho D R hr
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hP0 : 0<P η σ D R := lt_of_lt_of_le (by norm_num) hmargin.2.1
  have hpP : 1000*Real.log (Nat.card K)≤(momentOrder σ (P η σ D R):ℝ)*((L₀:ℝ)*R) := by
    rw [hq,Real.log_exp,hPL]
    have ht := (div_le_iff₀ hP0).mp hplo
    linarith only [ht,hσ]
  have hB : 0<geometryScale (Nat.card K) S.card := by
    unfold geometryScale
    have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    positivity
  have ht0 : 0<geometryScale (Nat.card K) S.card*
      Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 := by positivity
  have hb0 : Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by linarith only [hf])
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add,hq,←Real.exp_nat_mul];congr 1;norm_num;ring
  have hmoment := actual_high_radial_moment x hdim S C hS a b c ha hb hc F hF hf hn L₀
    (by simpa only [hL] using hbudget.1) R (momentOrder σ (P η σ D R)) (residualOrder σ)
    hp hKR hhpos hhsize herr hx (Real.exp (σ/5))
    (Real.one_le_exp_iff.mpr (by linarith only [hσ])) hcap
    (by simpa only [hPL] using hlocal.2.1)
    (by simpa only [coe_pointStrength] using hlocal.1) Lines hLines Q hxQ
    (by simpa only [hPL] using hgood) (by simpa only [hPL] using hPow)
    (by simpa only [coe_pointStrength,mul_comm (R:ℝ) (L₀:ℝ),hPL] using hlocal.2.2)
    (by simpa only [hL,pencilHighBudget,ParameterHierarchy.P] using hbudget.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.2) hstrong
    (by simpa only [hPL] using hbudget.2.2.1)
  have hprob := unsampled_score_tail x S (C a∪C b) L₀ (pointStrength S) F
    (fun H hH => (hF H hH).1) hb0 heven ht0 hmoment
  have hpoly := ScoreScalars.high_tail_polynomial hB
    (by exact_mod_cast (Nat.card_pos (α:=K)) : (0:ℝ)<Nat.card K)
    (momentOrder σ (P η σ D R))
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) hpP
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L₀*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans (add_le_add hpoly (le_refl _)))
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end

section
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_local_trunc_scalar_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g : ℝ,Range η σ D R → P η σ D R/20000≤g →
      localTruncConstant*σ*(P η σ D R)^5000*
        Real.exp (P η σ D R/100-4901*g)≤1 := by
  have hab := eventually_power_absorption hη hη' localTruncConstant 5001 (1/10)
    localTruncConstant_pos (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R g hr hg
  have hp := (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hp
  have hPσ : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hc : localTruncConstant*σ*(P η σ D R)^5000≤Real.exp (P η σ D R/10) := by
    calc
      _ ≤ localTruncConstant*σ*σ^5000 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hP0 hPσ _) (mul_nonneg localTruncConstant_pos.le (by linarith))
      _ = localTruncConstant*σ^(5001:ℕ) := by rw [show σ^(5001:ℕ)=σ^5000*σ from pow_succ σ 5000]; ac_rfl
      _ ≤ _ := by
        have hh := hab D R hr
        rw [show σ^(5001:ℝ)=σ^(5001:ℕ) from Real.rpow_natCast σ 5001] at hh
        simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using hh
  calc
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/100-4901*g) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+(P η σ D R/100-4901*g)) := (Real.exp_add ..).symm
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

theorem eventually_high_local_budget_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q m : ℕ) (n D : ℝ) (R : ℕ),
      (q:ℝ)=Real.exp σ → 0<n → (m:ℝ)≤Real.exp (3*σ) →
      Range η σ D R → (q:ℝ)^2*Real.exp (P η σ D R/20000)≤n →
      ((q:ℝ)/n*((q:ℝ)+1)≤2) ∧
      (208*2^198:ℝ)≤Real.exp (2*(P η σ D R/100)) ∧
      (pencilAlphabet q 3:ℝ)*(P η σ D R)^5000*
        (((q:ℝ)/n*((q:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 m:ℝ)+1)*
            ((q:ℝ)^4/n^2*Real.exp (P η σ D R/100))))≤geometryScale q n := by
  have ht := eventually_local_trunc_scalar_retained hη hη'
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
  have hg : P η σ D R/20000≤g := by
    rw [hq2,hnexp,←Real.exp_add,Real.exp_le_exp] at hnlo
    linarith
  have hg0 : 0≤g := (by positivity : 0≤P η σ D R/20000).trans hg
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
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_high_original_tail_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (5*σ/2) →
      (Nat.card K:ℝ)^2*Real.exp (P η σ D R/20000)≤(S.card:ℝ) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      ∀ (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
        x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
          (((pointStrength S:ℝ)*2^i)/2) Lines Q
          ((Nat.card K:ℝ)^4/S.card^2*Real.exp (P η σ D R/100)/
            (((pointStrength S:ℝ)*2^i)/2)^100)) →
      ((∑z : WeightedPrograms.DistinctPairs F,WeightedPrograms.strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
        dyadFactor (outsideAt x S (C a∪C b)).card (P η σ D R/100)*
          (geometryScale (Nat.card K) S.card)^2) →
      x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 →
      geometryScale (Nat.card K) S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ))+
      ∫ω,1-HighMoment.allTrunc R 5000 ω
        ∂batchMeasure (fun i : Fin R×RadialLine x => L₀*
          radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2) := by
  have hh := eventually_high_geometric_budget hη hη'
  have hl := eventually_high_local_budget_retained hη hη'
  have ho := eventually_moment_orders hη hη'
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),hh,hl,ho,hm] with σ hσ hh hl ho hm
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hShigh hn hf hF hx Lines Q hLines hxQ hgood hPow hstrong ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hcard : ((outsideAt x S (C a∪C b)).card:ℝ)≤Real.exp (3*σ) := by
    have hsub : (outsideAt x S (C a∪C b)).card≤S.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        have hy' : y.val∈S\(C a∪C b) := by simpa [outsideAt] using hy
        exact (Finset.mem_sdiff.mp hy').1
      · intro y hy z hz he
        exact Subtype.ext he
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr hsub
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := by
        exact mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hbudget := hh (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hSn hcard hr
  have hlocal := hl (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hcard hr hShigh
  obtain ⟨heven,hp,hplo,hphi,hps,hKR,hhpos,hhsize,herr⟩ := ho D R hr
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hP0 : 0<P η σ D R := lt_of_lt_of_le (by norm_num) hmargin.2.1
  have hpP : 1000*Real.log (Nat.card K)≤(momentOrder σ (P η σ D R):ℝ)*((L₀:ℝ)*R) := by
    rw [hq,Real.log_exp,hPL]
    have ht := (div_le_iff₀ hP0).mp hplo
    linarith only [ht,hσ]
  have hB : 0<geometryScale (Nat.card K) S.card := by
    unfold geometryScale
    have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    positivity
  have ht0 : 0<geometryScale (Nat.card K) S.card*
      Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 := by positivity
  have hb0 : Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by linarith only [hf])
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add,hq,←Real.exp_nat_mul];congr 1;norm_num;ring
  have hmoment := actual_high_radial_moment x hdim S C hS a b c ha hb hc F hF hf hn L₀
    (by simpa only [hL] using hbudget.1) R (momentOrder σ (P η σ D R)) (residualOrder σ)
    hp hKR hhpos hhsize herr hx (Real.exp (σ/5))
    (Real.one_le_exp_iff.mpr (by linarith only [hσ])) hcap
    (by simpa only [hPL] using hlocal.2.1)
    (by simpa only [coe_pointStrength] using hlocal.1) Lines hLines Q hxQ
    (by simpa only [hPL] using hgood) (by simpa only [hPL] using hPow)
    (by simpa only [coe_pointStrength,mul_comm (R:ℝ) (L₀:ℝ),hPL] using hlocal.2.2)
    (by simpa only [hL,pencilHighBudget,ParameterHierarchy.P] using hbudget.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.2) hstrong
    (by simpa only [hPL] using hbudget.2.2.1)
  have hprob := unsampled_score_tail x S (C a∪C b) L₀ (pointStrength S) F
    (fun H hH => (hF H hH).1) hb0 heven ht0 hmoment
  have hpoly := ScoreScalars.high_tail_polynomial hB
    (by exact_mod_cast (Nat.card_pos (α:=K)) : (0:ℝ)<Nat.card K)
    (momentOrder σ (P η σ D R))
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) hpP
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L₀*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans (add_le_add hpoly (le_refl _)))
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end SharpRamseyFive.ScoreGeometry

end OAI
