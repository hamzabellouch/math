import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Iteration.CellScoreProcedure
import OAI.Combinatorics.RamseyFive.Geometry.PlaneStrongExceptions

namespace OAI

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

lemma integral_filter_card {Ω A : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] [DecidableEq A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset A) (E : A→Set Ω) :
    (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)=∑x∈U,μ.real (E x) := by
  exact integral_failureCount μ U (fun x ω => ω∈E x)

lemma integral_filter_card_le {Ω A : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] [DecidableEq A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U bad : Finset A) (E : A→Set Ω) {e : ℝ} (he : 0≤e)
    (hprob : ∀x∈U\bad,μ.real (E x)≤e) :
    (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤(bad.card:ℝ)+U.card*e := by
  have h := expected_failureCount_le μ U bad (fun x ω => ω∈E x) (fun _ => 0) he
    (fun _ _ => le_rfl) (fun x hx => by
      simpa only [add_zero,Set.ofPred_mem_eq] using
        hprob x (by simpa only [Finset.mem_sdiff] using hx))
  simpa only [failureCount,Finset.sum_const_zero,add_zero] using h

end SharpRamseyFive.PoissonScore
namespace SharpRamseyFive.ScoreScalars

lemma regular_training_payment {L P : ℝ} (hL : 100000000≤L) (hLP : 100*L≤P) :
    200000*Real.exp (-2*(L/100))+Real.exp (-P/2)≤Real.exp (-L/1000) := by
  have h₁ := exp_sub_le_scaled (a:=L/1000) (b:=2*(L/100)) (C:=400000) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤400000),hL])
  have h₂ := exp_sub_le_scaled (a:=L/1000) (b:=P/2) (C:=2) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤2),hL,hLP])
  simp only [neg_div,neg_mul] at *
  linarith only [h₁,h₂]

lemma ambient_two_payment {σ : ℝ} (hσ : 100≤σ) :
    2*Real.exp (2*σ)*(Real.exp σ)^(-(50:ℝ))≤1/2 := by
  rw [←Real.exp_mul, mul_assoc,←Real.exp_add]
  have h := exp_sub_le_scaled (a:=0) (b:=48*σ) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hσ])
  simp only [neg_zero,Real.exp_zero] at h
  have he : 2*σ+σ*(-50)=-(48*σ) := by ring
  rw [he]
  linarith only [h]

end SharpRamseyFive.ScoreScalars

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_integrals {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
      (ia ib ic : ℙ K V→J),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (S.card:ℝ)≤10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤(S.card:ℝ) := by
  have ht := eventually_two_score_tails hη hη' Cb hCb
  have hm := eventually_score_margins hη hη' Cb hCb
  have hl := eventually_hierarchy hη hη' Cb 1 100000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hm,hl] with σ hσ ht hm hl
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ _ J _ U S C ia ib ic hdim hq hr hL hb₀ hbhi hτ
    hS hC hCS hCc hSn hn hf
  dsimp only
  let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
  let O := fun x => C (ia x)∪C (ib x)
  let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
  let bad := irregular (d:=2) S C ((L₀:ℝ)/100)
  let E : ℙ K V→Set (Fin R→S→ℕ) := fun x => {ω | Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\exceptional S C) (ctr x) ω|}
  have hn1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hlarge : 100000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτ).1
  have hLP : 100*(L₀:ℝ)≤P η σ D R := by rw [hL];exact (hm D b₀ τ R hr hb₀ hbhi hτ).2.2.2.1
  have hbad := irregular_card_bound (d:=2) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have htail (x : ℙ K V) (hx : x∉bad) :
      μ.real (E x)≤Real.exp (-P η σ D R/2) ∧ μ.real (E x)≤(Nat.card K:ℝ)^(-(50:ℝ)) := by
    apply ht D b₀ τ R L₀ K V x S C (ia x) (ib x) (ic x) (pencil x\exceptional S C) t
      hdim hq hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) hSn hn (hf x) _ hx (le_refl _)
    intro H hH
    have hh := Finset.mem_sdiff.mp hH
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩
  constructor
  · have hh := integral_filter_card_le μ S bad E (Real.exp_nonneg _)
      (fun x hx => (htail x (Finset.mem_sdiff.mp hx).2).1)
    change (∫ω,((S.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=(bad.card:ℝ)+S.card*Real.exp (-P η σ D R/2)) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    calc
      _ ≤ 200000*(S.card:ℝ)*Real.exp (-2*((L₀:ℝ)/100))+S.card*Real.exp (-P η σ D R/2) :=
        add_le_add hbad le_rfl
      _ = (S.card:ℝ)*(200000*Real.exp (-2*((L₀:ℝ)/100))+Real.exp (-P η σ D R/2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ScoreScalars.regular_training_payment hlarge hLP) (Nat.cast_nonneg _)
  · have hh := integral_filter_card_le μ U bad E (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun x hx => (htail x (Finset.mem_sdiff.mp hx).2).2)
    change (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=(bad.card:ℝ)+U.card*(Nat.card K:ℝ)^(-(50:ℝ))) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
    have hq2 : (2:ℝ)≤Nat.card K := by rw [hq];linarith only [Real.add_one_le_exp σ,hσ]
    have hU : (U.card:ℝ)≤2*Real.exp (2*σ) := by
      have hp := Finset.card_le_univ U
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim] at hp
      norm_num [Finset.sum_range_succ] at hp
      have hh : (U.card:ℝ)≤1+Nat.card K+(Nat.card K:ℝ)^2 := by exact_mod_cast hp
      have hqpow : (Nat.card K:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul];norm_num
      rw [←hqpow]
      nlinarith only [hh,hq2]
    have hpay := ScoreScalars.ambient_two_payment hσ
    have hu : (U.card:ℝ)*(Nat.card K:ℝ)^(-(50:ℝ))≤1/2 := by
      rw [hq]
      exact (mul_le_mul_of_nonneg_right hU (by positivity)).trans hpay
    have hrpay := ScoreScalars.exp_sub_le_scaled (a:=0) (b:=2*((L₀:ℝ)/100)) (C:=400000) (by norm_num)
      (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤400000),hlarge])
    simp only [neg_zero,Real.exp_zero] at hrpay
    rw [show -(2*((L₀:ℝ)/100))=(-2)*((L₀:ℝ)/100) by ring] at hrpay
    have hb : (bad.card:ℝ)≤(S.card:ℝ)/2 := by
      apply hbad.trans
      nlinarith only [mul_le_mul_of_nonneg_right hrpay (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]
    linarith only [hb,hu,hn1]

end SharpRamseyFive.ScoreGeometry

end OAI
