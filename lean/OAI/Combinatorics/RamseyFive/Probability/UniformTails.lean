import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.DimensionalScale
import OAI.Combinatorics.RamseyFive.Geometry.RowPowerTail
import OAI.Combinatorics.RamseyFive.Geometry.PlaneAnchor
import OAI.Combinatorics.RamseyFive.Geometry.ValidationOriginalTailWide

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

theorem eventually_score_slack {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb A k c : ℝ) (hCb : 0≤Cb) (hk : 1≤k) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R b τ : ℝ,Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      b+k*P η σ D R*τ+A≤c*L η σ D := by
  have hk0 : 0<k := by linarith
  have he := eventually_hierarchy hη hη' Cb (c/(2*k)) (2*max A 0/c) hCb (by positivity)
  filter_upwards [he] with σ he
  intro D R b τ hr hb hbhi hτ
  have hs := he D R b τ hr hbhi hτ
  have hA : A≤c*L η σ D/2 := by
    have hh := (div_le_iff₀ hc).mp hs.1
    linarith [le_max_left A 0]
  have hB : b+k*P η σ D R*τ≤k*(b+P η σ D R*τ) := by nlinarith only [hb,hk]
  have hh := mul_le_mul_of_nonneg_left hs.2.2.2.2.1 hk0.le
  have hx : k*(c/(2*k)*L η σ D)=c*L η σ D/2 := by field_simp
  rw [hx] at hh
  linarith only [hA,hB,hh]

theorem eventually_R_le_L {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    {c : ℝ} (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R : ℝ,Range η σ D R → R≤c*L η σ D := by
  have hb : 0<8*beta η := mul_pos (by norm_num) (beta_pos hη)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (4/c))] with σ hσ hlarge
  intro D R hr
  have hs : 0<σ := by linarith
  obtain ⟨hD,hR,hpow,hL,hLhi,hP,hPhi⟩ := finite_bounds hη hη' hσ hr
  have hR' : R≤4*σ^beta η := hr.rhi.trans (by linarith)
  have h4 : 4≤c*σ^(8*beta η) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    nlinarith only [hh]
  calc
    R ≤ 4*σ^beta η := hR'
    _ ≤ (c*σ^(8*beta η))*σ^beta η := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = c*σ^(9*beta η) := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    _ ≤ c*L η σ D := mul_le_mul_of_nonneg_left hL hc.le

theorem eventually_score_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ),Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      let ℓ := L η σ D
      let Q := P η σ D R
      let κ := b+8*Q*τ+Real.log 16
      1000000≤ℓ ∧ 100000≤Q ∧ (R:ℝ)≤Q/100000 ∧ 100*ℓ≤Q ∧
      (R:ℝ)*Real.log ℓ≤Q/100 ∧ κ+Real.log 10≤Q/20 ∧
      κ+Real.log 100≤(91/100:ℝ)*ℓ ∧
      (R:ℝ)*Real.exp (-(23/25:ℝ)*ℓ)≤1/10 := by
  have hs := eventually_score_slack hη hη' Cb (Real.log 16+Real.log 100+Real.log 10) 8
    (1/100) hCb (by norm_num) (by norm_num)
  have hh := eventually_hierarchy hη hη' Cb (1/100) 1000000 hCb (by norm_num)
  have hr := eventually_R_le_L hη hη' (c:=1) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hs,hh,hr] with σ hσ hs hh hr
  intro D b τ R hRange hb hbhi hτ
  dsimp only
  have hs := hs D R b τ hRange hb hbhi hτ
  have hh := hh D R b τ hRange hbhi hτ
  have hr : (R:ℝ)≤L η σ D := by simpa using hr D R hRange
  let ℓ := L η σ D
  let Q := P η σ D R
  have hL : 1000000≤ℓ := hh.1
  have hL0 : 0≤ℓ := by linarith only [hL]
  have hR1 : 1≤(R:ℝ) := (finite_bounds hη hη' hσ hRange).2.2.1.trans hRange.rlo
  have hP : ℓ≤Q := by dsimp [Q,P];nlinarith only [hR1,hL0]
  have hRsmall : (R:ℝ)≤Q/100000 := by dsimp [Q,P];nlinarith only [hL,(Nat.cast_nonneg R : (0:ℝ)≤R)]
  have hLP : 100*ℓ≤Q := by nlinarith only [hh.2.2.2.2.2]
  have hlog10 : 0≤Real.log 10 := Real.log_nonneg (by norm_num)
  have hlog100 : 0≤Real.log 100 := Real.log_nonneg (by norm_num)
  have hκP : b+8*Q*τ+Real.log 16+Real.log 10≤Q/20 := by
    change b+8*Q*τ+(Real.log 16+Real.log 100+Real.log 10)≤(1/100:ℝ)*ℓ at hs
    linarith only [hs,hlog100,hP,hL0]
  have hκL : b+8*Q*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*ℓ := by
    linarith only [hs,hlog10,hL0]
  refine ⟨hL,by linarith only [hL,hP],hRsmall,hLP,?_,hκP,hκL,?_⟩
  · simpa only [div_eq_mul_inv,mul_comm (100⁻¹:ℝ),one_mul] using hh.2.2.2.1
  · have he : ℓ≤Real.exp (ℓ/2) := by
      have he := Real.add_one_le_exp (ℓ/4)
      have hp : 0≤ℓ/4+1 := by positivity
      have hh := mul_self_le_mul_self hp he
      rw [←Real.exp_add] at hh
      have hex : ℓ/4+ℓ/4=ℓ/2 := by ring
      rw [hex] at hh
      nlinarith only [hh,sq_nonneg (ℓ/4-1)]
    have he2 : Real.exp (-(21/50:ℝ)*ℓ)≤1/10 := by
      have hx : (10:ℝ)≤Real.exp ((21/50:ℝ)*ℓ) := by
        linarith [Real.add_one_le_exp ((21/50:ℝ)*ℓ)]
      rw [show -(21/50:ℝ)*ℓ=-((21/50:ℝ)*ℓ) by ring,Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) hx
    calc
      _ ≤ Real.exp (ℓ/2)*Real.exp (-(23/25:ℝ)*ℓ) :=
        mul_le_mul_of_nonneg_right (hr.trans he) (Real.exp_nonneg _)
      _ = Real.exp (-(21/50:ℝ)*ℓ) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := he2

end SharpRamseyFive.ParameterHierarchy

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_validation_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (d : ℕ) (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=d+1 → 2≤d → d≤4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
      (∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun z:{z : F × F // z.1≠z.2} =>
          u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
            (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200≤
          (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
      scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  have ho := eventually_moment_orders hη hη'
  filter_upwards [eventually_ge_atTop (20:ℝ),hm,ho] with σ hσ hm ho
  intro d D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hd hd' hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hn hf hF hx hpairs ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hrat := dimensional_budget_ratios hd hd' hσ hq hsn hSn
  have hcard : (F.card:ℝ)≤400*(scale (K:=K) d S.card)^2 := by
    have hp := pencil_size x F (fun H hH => (hF H hH).1)
    rw [hdim,show d+1-1=d by omega] at hp
    have hc : (F.card:ℝ)≤(pencilAlphabet (Nat.card K) d:ℝ) := by exact_mod_cast hp
    have hB : 0<dimensionalScale (Nat.card K) d S.card := by
      exact lt_of_lt_of_le zero_lt_one hrat.1
    exact hc.trans (by simpa only [scale,dimensionalScale] using
      (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2)
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hR : 201≤R := by
    have hh := (ho D R hr).2.2.2.2.2.1
    omega
  simpa only [hPL] using validation_original_tail_wide x hdim (by omega) S C hS
    a b c ha hb hc F hF hf hn L₀ R hR (by simpa only [hPL] using hmargin.2.1)
    (by rw [hL]; linarith only [hmargin.1])
    (by simpa only [hPL] using hmargin.2.2.1)
    (by simpa only [hL,ParameterHierarchy.P] using hmargin.2.2.2.1)
    (by simpa only [hL,ParameterHierarchy.P] using hmargin.2.2.2.2.1)
    hx hcard (by simpa only [hPL] using hpairs)
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) ht

end

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem low_original_tail {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (heven : Even p) (hKR : 200≤R/2)
    (hh : 0<h) (hsize : h≤(R/2)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1≤cut)
    (hpairs : ∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
        (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
        scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
        scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
      2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
        (scale (K:=K) d S.card) cut L p R
        (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5))
    {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
    (hpP : 1000*Real.log (Nat.card K)≤(p:ℝ)*((L:ℝ)*R))
    (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
        (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
      (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have hB : 0<scale (K:=K) d S.card := by
    unfold scale
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have ht0 : 0<scale (K:=K) d S.card*Real.exp (-κ)/10 := by positivity
  have hb0 : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have : 0≤1-ownFraction S (C a) (C b) := by linarith only [hf]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) this
  have hm := actual_low_radial_moment x hdim hd S C hS a b c ha hb hc F hF hf hn
    L hL R p h hp hKR hh hsize herr hx cut hcut hpairs hrows hdegree hdegreeScalar
    hp2 hpairScalar hcost
  have hprob := unsampled_untruncated_tail x S (C a∪C b) L (pointStrength S) F
    (fun H hH => (hF H hH).1) hb0 heven ht0 hm
  have herr := ScoreScalars.high_tail_polynomial hB
    (by exact_mod_cast (Nat.card_pos (α:=K)) : (0:ℝ)<Nat.card K) p hκ hpP
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans herr)
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_low_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (d : ℕ) (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=d+1 → 2≤d → d≤4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
      (∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
          u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
            (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
          (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
      (∀H:F,∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
          (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
          scale (K:=K) d S.card*Real.exp (P η σ D R/50)) →
      (∀H:F,
        ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(momentOrder σ (P η σ D R):ℝ)) ≤ mass
          (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
          scale (K:=K) d S.card*Real.exp (-3*P η σ D R)) →
      scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have hh := eventually_low_geometric_budget hη hη'
  have ho := eventually_moment_orders hη hη'
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),hh,ho,hm] with σ hσ hh ho hm
  intro d D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hd hd' hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hSlow hn hf hF hx hpairs hrows hdegree ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hcard : ((outsideAt x S (C a∪C b)).card:ℝ)≤Real.exp (3*σ) := by
    have hsub : (outsideAt x S (C a∪C b)).card≤S.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        have hy' : y.val∈S\(C a∪C b) := by simpa [outsideAt] using hy
        exact (Finset.mem_sdiff.mp hy').1
      · intro y hy z hz he
        exact Subtype.ext he
    have hdR : (d:ℝ)≤4 := by exact_mod_cast hd'
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith [Real.add_one_le_exp (σ/2)]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr hsub
      _ ≤ 10*Real.exp (((d:ℝ)+1)*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := by
        apply mul_le_mul he (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hbudget := hh (Nat.card K) d (outsideAt x S (C a∪C b)).card S.card D R
    hd hd' hq hsn hSn hSlow hcard hr
  obtain ⟨heven,hp,hplo,hphi,hps,hKR,hhpos,hhsize,herr⟩ := ho D R hr
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hP0 : 0<P η σ D R := lt_of_lt_of_le (by norm_num) hmargin.2.1
  have hpP : 1000*Real.log (Nat.card K)≤(momentOrder σ (P η σ D R):ℝ)*((L₀:ℝ)*R) := by
    rw [hq,Real.log_exp,hPL]
    have ht := (div_le_iff₀ hP0).mp hplo
    linarith
  apply low_original_tail x hdim hd S C hS a b c ha hb hc F hF hf hn L₀
    (by simpa only [hL] using hbudget.1) R (momentOrder σ (P η σ D R)) (residualOrder σ)
    hp heven hKR hhpos (hhsize.trans (Nat.div_le_div_right (Nat.sub_le _ _))) herr hx
    (Real.exp (σ/5)) (Real.one_le_exp_iff.mpr (by linarith))
    (by simpa only [hPL] using hpairs) (by simpa only [hPL] using hrows)
    (by simpa only [hPL] using hdegree)
    (by simpa only [hPL,scale,dimensionalScale] using hbudget.2.2.2.2)
    (by simpa only [hPL] using hbudget.2.2.2.1)
    (by simpa only [hPL,scale,dimensionalScale] using hbudget.2.2.1)
    (by simpa only [hL,scale,dimensionalScale,ParameterHierarchy.P] using hbudget.2.1)
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) hpP ht

end SharpRamseyFive.ScoreGeometry

end OAI
