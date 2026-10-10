import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.ValidationOriginalTailWide

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma exp_sub_le_scaled {a b C : ℝ} (hC : 0<C) (h : a+Real.log C≤b) :
    C*Real.exp (-b)≤Real.exp (-a) := by
  rw [←Real.exp_log hC,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [h])

theorem procedure_probability {q B n P L u κ z M βS βU C : ℝ}
    (hq : 10≤q) (hB : 0<B) (hn : 0<n) (hP : 0≤P)
    (hz : q*B*Real.exp (-κ)≤z) (hM : M≤100000*q*B)
    (hβS : βS≤n*Real.exp (-L/1000)) (hβU : βU≤n*Real.exp (C*P))
    (he : κ+u+Real.log 3200000000≤P/2000)
    (hs : u+Real.log 1600≤L/1000) (hu : u+Real.log 16≤P) :
    Real.exp (-u)/4 ≤ Real.exp (-u)/2-
      M*Real.exp (-P/2000)/((1/2000:ℝ)*z)-βS/(n/100)-
      βU/(n*Real.exp ((C+1)*P))-Real.exp (-(q*P)/4) := by
  have hq0 : 0<q := by linarith only [hq]
  have hz0 : 0<z := lt_of_lt_of_le (by positivity) hz
  have hfirst : M*Real.exp (-P/2000)/((1/2000:ℝ)*z)≤Real.exp (-u)/16 := by
    have hbase : M/z≤100000*Real.exp κ := by
      apply (div_le_iff₀ hz0).mpr
      calc
        M ≤ 100000*q*B := hM
        _ = (100000*Real.exp κ)*(q*B*Real.exp (-κ)) := by
          rw [show (100000*Real.exp κ)*(q*B*Real.exp (-κ))=
            (100000*q*B)*(Real.exp κ*Real.exp (-κ)) by ring,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
        _ ≤ (100000*Real.exp κ)*z := mul_le_mul_of_nonneg_left hz (by positivity)
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<3200000000) he
    have hhe : 200000000*Real.exp (κ-P/2000)≤Real.exp (-u)/16 := by
      calc
        _ = (3200000000*Real.exp (-(P/2000))*Real.exp κ)/16 := by
          rw [sub_eq_add_neg,Real.exp_add];ring
        _ ≤ (Real.exp (-(κ+u))*Real.exp κ)/16 := by gcongr
        _ = _ := by rw [←Real.exp_add];congr 2;ring
    calc
      _ = 2000*(M/z)*Real.exp (-P/2000) := by field_simp
      _ ≤ 2000*(100000*Real.exp κ)*Real.exp (-P/2000) := by gcongr
      _ = 200000000*Real.exp (κ-P/2000) := by rw [sub_eq_add_neg,Real.exp_add,neg_div];ring
      _ ≤ _ := hhe
  have hsecond : βS/(n/100)≤Real.exp (-u)/16 := by
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<1600) hs
    apply (div_le_iff₀ (by positivity : 0<n/100)).mpr
    have h := mul_le_mul_of_nonneg_left hh hn.le
    have hβ := hβS
    rw [show -L/1000=-(L/1000) by ring] at hβ
    nlinarith only [h,hβ]
  have hthird : βU/(n*Real.exp ((C+1)*P))≤Real.exp (-u)/16 := by
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<16) hu
    calc
      _ ≤ (n*Real.exp (C*P))/(n*Real.exp ((C+1)*P)) :=
        div_le_div_of_nonneg_right hβU (by positivity)
      _ = Real.exp (-P) := by
        rw [mul_div_mul_left _ _ hn.ne',←Real.exp_sub];congr 1;ring
      _ ≤ _ := (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr (by nlinarith only [hh])
  have hfourth : Real.exp (-(q*P)/4)≤Real.exp (-u)/16 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hq,hP]) :
      Real.exp (-(q*P)/4)≤Real.exp (-P))
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<16) hu
    linarith only [hh]
  linarith only [hfirst,hsecond,hthird,hfourth]

lemma procedure_output {n P κ C bad samples tail : ℝ} (hn : 0≤n)
    (hP : 104≤P) (hC : 0≤C) (hκ : κ≤P)
    (hbad : bad≤n/100) (hsamples : samples≤2*n) (htail : tail≤100*n*Real.exp κ) :
    samples+bad+n*Real.exp ((C+1)*P)+tail≤n*Real.exp ((C+2)*P) := by
  have hP0 : 0≤P := by linarith only [hP]
  have hPC : P≤(C+1)*P := by nlinarith only [hC,hP0]
  have he1 : 1≤Real.exp ((C+1)*P) := Real.one_le_exp_iff.mpr (by nlinarith only [hC,hP0])
  have heP : (104:ℝ)≤Real.exp P := by linarith only [Real.add_one_le_exp P,hP]
  have heκ : Real.exp κ≤Real.exp ((C+1)*P) := Real.exp_le_exp.mpr (hκ.trans hPC)
  calc
    _ ≤ 104*n*Real.exp ((C+1)*P) := by
      have h1 := mul_le_mul_of_nonneg_left he1 hn
      have h2 := mul_le_mul_of_nonneg_left heκ (mul_nonneg (by norm_num : (0:ℝ)≤100) hn)
      nlinarith only [hbad,hsamples,htail,h1,h2,hn]
    _ ≤ n*(Real.exp P*Real.exp ((C+1)*P)) := by
      have h := mul_le_mul_of_nonneg_left heP (mul_nonneg hn (Real.exp_pos ((C+1)*P)).le)
      nlinarith only [h]
    _ = _ := by rw [←Real.exp_add];congr 2;ring

end SharpRamseyFive.ScoreScalars

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma thin_empty_lower {d : ℕ} (X S : Finset (ℙ K V)) (hS : S⊆X) (hS0 : S.Nonempty)
    (hret : X.card≤4*S.card) (T : Finset (ℙ K (Dual K V)))
    {τ b P : ℝ} (hτ : 0<τ)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
    (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card) :
    let T₀ := T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ
    (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-(b+8*P*τ+Real.log 16))≤
      (T₀.card:ℝ)*Real.exp (-P*(8*τ))/2 := by
  have hthin := thin_hyperplanes X S hS hS0 hret T hτ hdensity
  dsimp only at hthin ⊢
  have hn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS0.card_pos
  have hr : (X.card:ℝ)≤4*(S.card:ℝ) := by exact_mod_cast hret
  have hT : (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-b)/4≤(T.card:ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    dsimp only [scale]
    rw [←mul_div_assoc,mul_comm (Nat.card K:ℝ) _,←pow_succ,div_mul_eq_mul_div]
    apply (div_le_iff₀ hn).mpr
    have ht := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg T.card : (0:ℝ)≤T.card)
    nlinarith only [hprod,ht]
  have ht := mul_le_mul_of_nonneg_right hT (Real.exp_nonneg (-P*(8*τ)))
  have hh := mul_le_mul_of_nonneg_right hthin (Real.exp_nonneg (-P*(8*τ)))
  have he : Real.exp (-(b+8*P*τ+Real.log 16))=
      (Real.exp (-b)*Real.exp (-P*(8*τ)))/16 := by
    rw [show -(b+8*P*τ+Real.log 16)=-b+-P*(8*τ)-Real.log 16 by ring,
      Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<16)]
  rw [he]
  nlinarith only [ht,hh]

omit [Finite K] [FiniteDimensional K V] in
lemma regular_exceptional_count {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V) (ξ : ℝ)
    (hx : x∉irregular (d:=d) S C ξ) :
    ((pencil x∩exceptional S C).card:ℝ)≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hh : ¬∃j:Option (Option J),scale (K:=K) d S.card*Real.exp ξ<
      weightOnPencil (clippedWeight S C j) x := by
    simpa only [irregular,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  have h := le_of_not_gt (fun h => hh ⟨none,h⟩)
  convert! h using 1
  simp only [weightOnPencil,clippedWeight,incidenceEntry]
  simp only [mul_ite,mul_one,mul_zero]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_boole]
  congr 2
  ext H
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,pencil]
  tauto

omit [FiniteDimensional K V] in
lemma regular_centering {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (_hS : S.Nonempty)
    (x : ℙ K V) {L f κ z : ℝ} {R : ℕ} (hL : 0≤L) (hf : f≤2/25)
    (hx : x∉irregular (d:=d) S C (L/100))
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*L)≤1/10)
    (hκ : κ+Real.log 100≤(91/100:ℝ)*L)
    (hz : (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-κ)≤z) :
    let b := Real.exp (-L*(1-f))
    b∈Set.Icc 0 1 ∧ 9/10≤(1-b)^R ∧
      b*(pencil x∩exceptional S C).card≤z/(100*(Nat.card K:ℝ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hB : 0≤ scale (K:=K) d S.card := scale_nonneg _ _ (Nat.cast_nonneg _)
  have he := ScoreScalars.exp_sub_le_scaled (by norm_num : (0:ℝ)<100) hκ
  have herr : scale (K:=K) d S.card*Real.exp (-(91/100:ℝ)*L)≤z/(100*(Nat.card K:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<100*(Nat.card K:ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hq.le hB)
    rw [show -(91/100:ℝ)*L=-((91/100:ℝ)*L) by ring]
    nlinarith only [hh,hz]
  obtain ⟨hb,hc,he⟩ := ScoreScalars.exceptional_scales hL hf hB hq hR herr
  refine ⟨hb,hc,?_⟩
  exact (mul_le_mul_of_nonneg_left (regular_exceptional_count S C x (L/100) hx) (Real.exp_pos _).le).trans he

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem cell_score_from_integrals {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (X U S : Finset (ℙ K V)) (hSX : S⊆X) (hSU : S⊆U)
    (hS : S.Nonempty) (hret : X.card≤4*S.card)
    {J : Type*} [Fintype J] (C : J→Finset (ℙ K V))
    (hC : (∑j,(C j).card)≤3*S.card) (ia ib : ℙ K V→J)
    (hf : ∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25)
    (T : Finset (ℙ K (Dual K V))) (L : ℝ≥0) (R : ℕ) (b τ CP : ℝ)
    (hτ : 0<τ) (hτhi : 8*τ≤4/5)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
    (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hP : 104≤(L:ℝ)*R) (hCP : 0≤CP)
    (hnP : (Nat.card K:ℝ)*((L:ℝ)*R)≤S.card)
    (hbad : ((irregular (d:=d) S C ((L:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100)
    (he : b+16*((L:ℝ)*R)*τ+Real.log 16+Real.log 3200000000≤((L:ℝ)*R)/2000)
    (hs : 8*((L:ℝ)*R)*τ+Real.log 1600≤(L:ℝ)/1000)
    (hu : 8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hk : b+8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hκL : b+8*((L:ℝ)*R)*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*(L:ℝ))
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*(L:ℝ))≤1/10)
    (htrain : (∫ω,((typicalFailures S S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (-(L:ℝ)/1000))
    (hamb : (∫ω,((typicalFailures U S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (CP*((L:ℝ)*R))) :
    Real.exp (-8*((L:ℝ)*R)*τ)/4≤
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*((L:ℝ)*R)) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp ((CP+2)*((L:ℝ)*R)) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  let q : ℝ := Nat.card K
  let n : ℝ := S.card
  let P : ℝ := (L:ℝ)*R
  let B : ℝ := scale (K:=K) d S.card
  let κ : ℝ := b+8*P*τ+Real.log 16
  let T₀ := T.filter fun H => cellMass S (q/S.card) H≤8*τ
  let z : ℝ := (T₀.card:ℝ)*Real.exp (-P*(8*τ))/2
  let bad := irregular (d:=d) S C ((L:ℝ)/100)
  let O := fun x => C (ia x)∪C (ib x)
  let ctr := fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let μ := scheduleMeasure (fun _ : S => L*pointStrength S) R
  have hn : 0<n := Nat.cast_pos.mpr hS.card_pos
  have hq0 : 0<q := by dsimp [q];linarith only [hq]
  have hB : 0<B := by dsimp [B,scale];positivity
  have hz : q*B*Real.exp (-κ)≤z := thin_empty_lower X S hSX hS hret T hτ hdensity hprod
  have hz0 : 0<z := lt_of_lt_of_le (by positivity) hz
  have hT : T₀.Nonempty := Finset.card_pos.mp (by
    by_contra h
    have he : T₀.card=0 := by omega
    simp only [z,he,Nat.cast_zero,zero_mul,zero_div] at hz0
    exact lt_irrefl _ hz0)
  have hcenter : ∀x∈U\bad,ctr x∈Set.Icc 0 1 ∧ 9/10≤(1-ctr x)^R ∧
      ctr x*(pencil x∩exceptional S C).card≤z/(100*q) := by
    intro x hx
    exact regular_centering S C hS x L.coe_nonneg (hf x) (Finset.mem_sdiff.mp hx).2 hR hκL hz
  have ht : B*Real.exp (-κ)/10≤z/(10*q) := by
    apply (le_div_iff₀ (by positivity : 0<10*q)).mpr
    nlinarith only [hz]
  have hmono (A : Finset (ℙ K V)) :
      (∫ω,((typicalFailures A S O (exceptional S C) ctr (z/(10*q)) ω).card:ℝ) ∂μ)≤
      (∫ω,((typicalFailures A S O (exceptional S C) ctr (B*Real.exp (-κ)/10) ω).card:ℝ) ∂μ) := by
    apply integral_mono
    · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (A.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
    · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (A.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
    · intro ω
      exact Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono A S O (exceptional S C) ctr ht ω))
  have hevent := original_score_procedure hdim hd hq U S hSU hS O (exceptional S C) T₀ hT
    (thin_subset_exceptional S C hS T hτhi) ctr bad L R (8*τ) (100000*q*B)
    (fun H hH => (Finset.mem_filter.mp hH).2)
    (exceptional_mass_bound hdim hd S C hS hC)
    (n*Real.exp (-(L:ℝ)/1000)) (n*Real.exp (CP*P)) (n/100) (n*Real.exp ((CP+1)*P))
    (by positivity) (by positivity) (fun x hx => (hcenter x hx).1)
    (fun x hx => (hcenter x hx).2.1) (fun x hx => by
      simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hcenter x hx).2.2)
    (by simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hmono S).trans htrain)
    (by simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hmono U).trans hamb)
  dsimp only at hevent
  have hprob := ScoreScalars.procedure_probability (q:=q) (B:=B) (n:=n) (P:=P)
    (L:=L) (u:=8*P*τ) (κ:=κ) (z:=z) (M:=100000*q*B)
    (βS:=n*Real.exp (-(L:ℝ)/1000)) (βU:=n*Real.exp (CP*P)) (C:=CP)
    hq hB hn (by dsimp [P];positivity) hz le_rfl le_rfl le_rfl
    (by dsimp [κ];linarith only [he]) hs hu
  rw [show -(8*P*τ)=-P*(8*τ) by ring] at hprob
  have hh := hprob.trans hevent
  have htbound : 100*q^(d+1)/z≤100*n*Real.exp κ := by
    apply (div_le_iff₀ hz0).mpr
    calc
      _ = (100*n*Real.exp κ)*(q*B*Real.exp (-κ)) := by
        dsimp [B,scale,n,q]
        rw [show (100*(S.card:ℝ)*Real.exp κ)*((Nat.card K:ℝ)*
          ((Nat.card K:ℝ)^d/S.card)*Real.exp (-κ))=
          100*((Nat.card K:ℝ)^(d+1))*((S.card:ℝ)/S.card)*(Real.exp κ*Real.exp (-κ)) by
            rw [pow_succ];ring]
        rw [div_self hn.ne',←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one,mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have hout := ScoreScalars.procedure_output hn.le hP hCP hk hbad
    (show 2*(q*P)≤2*n from by linarith only [hnP]) htbound
  rw [show -8*((L:ℝ)*R)*τ= -P*(8*τ) by dsimp [P];ring]
  apply hh.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  refine ⟨hω.1,hω.2.1.trans hout,?_⟩
  change (9/10:ℝ)*n≤_
  have hc := hω.2.2
  change (99/100:ℝ)*n-(bad.card:ℝ)-n/100≤_ at hc
  change (bad.card:ℝ)≤n/100 at hbad
  linarith only [hc,hbad,hn]

end SharpRamseyFive.ScoreGeometry

end OAI
