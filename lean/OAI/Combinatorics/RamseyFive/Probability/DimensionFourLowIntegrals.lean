import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PlaneExceptions
import OAI.Combinatorics.RamseyFive.Geometry.DimensionFourLowValidation
import OAI.Combinatorics.RamseyFive.Geometry.DimensionFourLowAmbient

namespace OAI

namespace SharpRamseyFive.ScoreScalars
lemma ambient_four_payment {σ : ℝ} (hσ : 100≤σ) :
    2*Real.exp (4*σ)*(Real.exp σ)^(-(50:ℝ))≤1/2 := by
  rw [←Real.exp_mul, mul_assoc,←Real.exp_add]
  have h := exp_sub_le_scaled (a:=0) (b:=46*σ) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hσ])
  simp only [neg_zero,Real.exp_zero] at h
  have he : 4*σ+σ*(-50)=-(46*σ) := by ring
  rw [he]
  linarith only [h]
end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_low_score_integrals {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ {A : Type} [Fintype A] (g : ℝ) (F : Finset J) (hF : F.Nonempty)
      (Flat : J→Submodule K (I→K)) (X U S : Finset (ℙ K (I→K)))
      (t₀ : ℝ) (ht₀ : 0<t₀) (rawOwn : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (C : A→Finset (ℙ K (I→K))) (ia ib ic : ℙ K (I→K)→A),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → g≤2*σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t₀=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤10*Real.exp (5*σ/2) →
      (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀)) x⊆rawOwn x) →
      (∀x,S∩rawOwn x=C (ia x)∪C (ib x)) →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (8*P η σ D R) := by
  have ht := eventually_four_low_validation_tail hη hη' Cb hCb
  have hu := eventually_four_low_ambient_tail hη hη' Cb hCb
  have he := eventually_literal_plane_half_exceptions hη hη'
  have hm := eventually_score_margins hη hη' Cb hCb
  have hl := eventually_hierarchy hη hη' Cb 1 10000000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hu,he,hm,hl] with σ hσ ht hu he hm hl
  intro D b₀ τ R L₀ q K I J _ _ _ _ _ _ _ _ A _ g F hF Flat X U S t₀ ht₀ rawOwn C ia ib ic
    hq hcard hσq hI hr hL hb₀ hbhi hτ hg hFlat hcover hX htc hpeel hquarter hn hLow hraw hOwn hC hCS hCc hdiv hf
  dsimp only
  let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
  let O := fun x => C (ia x)∪C (ib x)
  let O' := fun x => S∩rawOwn x
  let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let t := scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
  let Lines := radialInventory (K:=K) (V:=I→K)
  let reg := irregular (d:=4) S C ((L₀:ℝ)/100)
  let rad := radialExceptions S O' (pointStrength S) Lines Finset.univ q S.card (P η σ D R/200)
  let strong := ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Finset.univ
  let bad := reg∪rad
  let E : ℙ K (I→K)→Set (Fin R→S→ℕ) := fun x =>
    {ω | Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\exceptional S C) (ctr x) ω|}
  have hSn0 : (0:ℝ)<S.card := (by positivity : (0:ℝ)<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn0)
  have hn1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hdim : finrank K (I→K)=5 := by simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hI
  have hqσ : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hSn : (S.card:ℝ)≤Real.exp (3*σ) := by
    have hx : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _≤10*Real.exp (5*σ/2) := hn
      _≤Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
      _=_ := by rw [←Real.exp_add];congr 1;ring
  have he := he D R hr q K I J g F hF Flat X S t₀ ht₀ rawOwn Lines Finset.univ
    hq hcard hσq (Or.inr hI) hg hFlat hcover hX htc hpeel hquarter hSn hraw radialInventory_rank
  have hrad : (rad.card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by simpa only [hL] using he.1
  have hstrong : (strong.card:ℝ)≤(S.card:ℝ)*Real.exp (7*P η σ D R) := he.2
  have hlarge : 10000000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτ).1
  have hLP : 100*(L₀:ℝ)≤P η σ D R := by rw [hL];exact (hm D b₀ τ R hr hb₀ hbhi hτ).2.2.2.1
  have hreg := irregular_card_bound (d:=4) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have hbad : (bad.card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*((L₀:ℝ)/100))+
      (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by
    exact (Nat.cast_le.mpr (Finset.card_union_le reg rad) |>.trans (by norm_cast)).trans (add_le_add hreg hrad)
  have hpay : (bad.card:ℝ)+S.card*Real.exp (-P η σ D R/2)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by
    have hh := mul_le_mul_of_nonneg_left (ScoreScalars.regular_training_payment_half hlarge hLP) hSn0.le
    nlinarith only [hh,hbad]
  have hbelow (x : ℙ K (I→K)) (H : ℙ K (Dual K (I→K))) (hH : H∈pencil x\exceptional S C) :
      Incident x H ∧ H∉exceptional S C := by
    have hh := Finset.mem_sdiff.mp hH
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩
  have htraining (x : ℙ K (I→K)) (hx : x∉bad) : μ.real (E x)≤Real.exp (-P η σ D R/2) := by
    have hx' : x∉reg ∧ x∉rad := ⟨fun h => hx (Finset.mem_union_left _ h),fun h => hx (Finset.mem_union_right _ h)⟩
    apply ht D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) O' (pencil x\exceptional S C)
      Lines Finset.univ t hdim hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) (hOwn x) hn hLow hdiv (hf x)
      (hbelow x) hx'.1 (mem_radialInventory x) (Finset.mem_univ _) _ (le_refl _)
    simpa only [hcard] using hx'.2
  have hambient (x : ℙ K (I→K)) (hx : x∉bad∪strong) : μ.real (E x)≤(Nat.card K:ℝ)^(-(50:ℝ)) := by
    have hh : x∉bad ∧ x∉strong := ⟨fun h => hx (Finset.mem_union_left _ h),fun h => hx (Finset.mem_union_right _ h)⟩
    have hx' : x∉reg ∧ x∉rad := ⟨fun h => hh.1 (Finset.mem_union_left _ h),fun h => hh.1 (Finset.mem_union_right _ h)⟩
    apply hu D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) O' (pencil x\exceptional S C)
      Lines Finset.univ t hdim hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) (hOwn x) hn hLow hdiv (hf x)
      (hbelow x) hx'.1 (mem_radialInventory x) (Finset.mem_univ _) _
      (off_ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Finset.univ x hh.2) (le_refl _)
    simpa only [hcard] using hx'.2
  constructor
  · have hh := integral_filter_card_le μ S bad E (Real.exp_nonneg _) (fun x hx => htraining x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((S.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans ?_ hpay
    convert hh using 1; try rfl
    apply integral_congr_ae
    filter_upwards with ω
    congr 2
    ext x
    simp only [Finset.mem_filter]
  · have hh := integral_filter_card_le μ U (bad∪strong) E (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun x hx => hambient x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=((bad∪strong).card:ℝ)+U.card*(Nat.card K:ℝ)^(-(50:ℝ))) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    have hq2 : (2:ℝ)≤Nat.card K := by rw [hqσ];linarith only [Real.add_one_le_exp σ,hσ]
    have hU : (U.card:ℝ)≤2*Real.exp (4*σ) := by
      have hp := Finset.card_le_univ U
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K (I→K) hdim] at hp
      norm_num [Finset.sum_range_succ] at hp
      have hh : (U.card:ℝ)≤1+Nat.card K+(Nat.card K:ℝ)^2+(Nat.card K:ℝ)^3+(Nat.card K:ℝ)^4 := by exact_mod_cast hp
      have hqpow : (Nat.card K:ℝ)^4=Real.exp (4*σ) := by rw [hqσ,←Real.exp_nat_mul];norm_num
      rw [←hqpow]
      have hqq : (Nat.card K:ℝ)^2≥2*Nat.card K := by nlinarith only [hq2]
      have hqqq : (Nat.card K:ℝ)^3≥2*(Nat.card K:ℝ)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hq2 (sq_nonneg (Nat.card K:ℝ))]
      have hqqqq : (Nat.card K:ℝ)^4≥2*(Nat.card K:ℝ)^3 := by
        nlinarith only [mul_le_mul_of_nonneg_right hq2 (pow_nonneg (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K) 3)]
      linarith only [hh,hq2,hqq,hqqq,hqqqq]
    have hu : (U.card:ℝ)*(Nat.card K:ℝ)^(-(50:ℝ))≤1/2 := by
      rw [hqσ]
      exact (mul_le_mul_of_nonneg_right hU (by positivity)).trans (ScoreScalars.ambient_four_payment hσ)
    have hbadn : (bad.card:ℝ)≤S.card := by
      have hexp : Real.exp (-(L₀:ℝ)/1000)≤1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by norm_num))
      have htpos : 0≤(S.card:ℝ)*Real.exp (-P η σ D R/2) := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
      have hb : (bad.card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by linarith only [hpay,htpos]
      exact hb.trans (mul_le_of_le_one_right hSn0.le hexp)
    have hP0 : 0≤P η σ D R := by linarith only [hLP,hlarge]
    have hPexp : (3:ℝ)≤Real.exp (P η σ D R) := by linarith only [Real.add_one_le_exp (P η σ D R),hLP,hlarge]
    have hexp7 : (1:ℝ)≤Real.exp (7*P η σ D R) := Real.one_le_exp (mul_nonneg (by norm_num) hP0)
    have hbadall : ((bad∪strong).card:ℝ)≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R) := by
      have hc : ((bad∪strong).card:ℝ)≤(bad.card:ℝ)+strong.card := by exact_mod_cast Finset.card_union_le bad strong
      exact hc.trans (add_le_add hbadn hstrong)
    calc
      _≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R)+1/2 := add_le_add hbadall hu
      _≤3*(S.card:ℝ)*Real.exp (7*P η σ D R) := by
        nlinarith only [mul_le_mul_of_nonneg_left hexp7 hSn0.le,hn1]
      _≤Real.exp (P η σ D R)*(S.card:ℝ)*Real.exp (7*P η σ D R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPexp (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _=_ := by rw [mul_assoc,mul_left_comm (Real.exp _),←Real.exp_add];congr 2;ring

end SharpRamseyFive.ScoreGeometry

end OAI
