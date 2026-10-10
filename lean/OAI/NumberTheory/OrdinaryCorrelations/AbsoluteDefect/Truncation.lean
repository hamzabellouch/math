import Mathlib

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
open Classical

namespace OrdinaryCorrelations.SourceBonferroni

def truncation (n r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r+1), (-1:ℝ)^k * n.choose k

lemma truncation_succ (n r : ℕ) :
    truncation (n+1) r = (-1:ℝ)^r * n.choose r := by
  have h := Int.alternating_sum_range_choose_eq_choose (n:=n) (m:=r)
  unfold truncation
  exact_mod_cast h

lemma truncation_zero (r : ℕ) : truncation 0 r = 1 := by
  unfold truncation
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
  · simp

theorem even_error (n r : ℕ) :
    0 ≤ truncation n (2*r) - (if n=0 then 1 else 0) ∧
    truncation n (2*r) - (if n=0 then 1 else 0) ≤ (n.choose (2*r+1) : ℝ) := by
  cases n with
  | zero => simp [truncation_zero]
  | succ n =>
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,sub_zero]
    have he : (-1:ℝ)^(2*r) = 1 := by rw [pow_mul]; norm_num
    rw [truncation_succ,he,one_mul]
    constructor
    · positivity
    · have hchoose : n.choose (2*r) ≤ (n+1).choose (2*r+1) := by
        rw [Nat.choose_succ_succ]
        omega
      exact_mod_cast hchoose

variable {ι Ω : Type*}

def badCount (s : Finset ι) (E : ι → Ω → Prop) (ω : Ω) : ℕ :=
  (s.filter (fun i => E i ω)).card

def joint (E : ι → Ω → Prop) (t : Finset ι) (ω : Ω) : ℝ :=
  if ∀ i ∈ t, E i ω then 1 else 0

def survives (s : Finset ι) (E : ι → Ω → Prop) (ω : Ω) : ℝ :=
  if ∀ i ∈ s, ¬ E i ω then 1 else 0

lemma joint_choose (s : Finset ι) (E : ι → Ω → Prop) (ω : Ω) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, joint E t ω) = (badCount s E ω).choose k := by
  have he : (s.powersetCard k).filter (fun t => ∀ i ∈ t, E i ω) =
      (s.filter (fun i => E i ω)).powersetCard k := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_iff]
    constructor
    · rintro ⟨⟨hsub,hcard⟩,he⟩
      exact ⟨fun i hi => ⟨hsub hi,he i hi⟩,hcard⟩
    · rintro ⟨hsub,hcard⟩
      exact ⟨⟨fun i hi => (hsub hi).1,hcard⟩,fun i hi => (hsub hi).2⟩
  unfold joint
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,he,Finset.card_powersetCard,badCount]
  ring

lemma survives_eq (s : Finset ι) (E : ι → Ω → Prop) (ω : Ω) :
    survives s E ω = if badCount s E ω = 0 then 1 else 0 := by
  have he : badCount s E ω = 0 ↔ ∀ i ∈ s, ¬ E i ω := by
    simp only [badCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  simp only [survives,he]

def intersectionMass (s : Finset Ω) (w : Ω → ℝ) (E : ι → Ω → Prop)
    (t : Finset ι) : ℝ := ∑ ω ∈ s, w ω * joint E t ω

def survivalMass (s : Finset Ω) (w : Ω → ℝ) (P : Finset ι) (E : ι → Ω → Prop) : ℝ :=
  ∑ ω ∈ s, w ω * survives P E ω

def eventTruncation (s : Finset Ω) (w : Ω → ℝ) (P : Finset ι)
    (E : ι → Ω → Prop) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r+1), (-1:ℝ)^k * ∑ t ∈ P.powersetCard k, intersectionMass s w E t

lemma eventTruncation_eq (s : Finset Ω) (w : Ω → ℝ) (P : Finset ι)
    (E : ι → Ω → Prop) (r : ℕ) :
    eventTruncation s w P E r = ∑ ω ∈ s, w ω * truncation (badCount P E ω) r := by
  unfold eventTruncation intersectionMass truncation
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    enter [2,k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.range (r+1)) (t := s)]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro k _
  rw [← joint_choose P E ω k]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem finite_bonferroni (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω)
    (P : Finset ι) (E : ι → Ω → Prop) (r : ℕ) :
    0 ≤ eventTruncation s w P E (2*r) - survivalMass s w P E ∧
    eventTruncation s w P E (2*r) - survivalMass s w P E ≤
      ∑ t ∈ P.powersetCard (2*r+1), intersectionMass s w E t := by
  rw [eventTruncation_eq]
  unfold survivalMass
  rw [← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro ω hω
    rw [← mul_sub,survives_eq]
    exact mul_nonneg (hw ω hω) (even_error (badCount P E ω) r).1
  · calc
      _ ≤ ∑ ω ∈ s, w ω * ((badCount P E ω).choose (2*r+1) : ℝ) := by
        apply Finset.sum_le_sum
        intro ω hω
        rw [← mul_sub,survives_eq]
        exact mul_le_mul_of_nonneg_left (even_error (badCount P E ω) r).2 (hw ω hω)
      _ = _ := by
        simp_rw [← joint_choose P E _ (2*r+1),Finset.mul_sum]
        exact Finset.sum_comm

def elementary (P : Finset ι) (v : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ P.powersetCard k, ∏ i ∈ t, v i

theorem elementary_le_exp (P : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ P, 0 ≤ v i) (k : ℕ) :
    elementary P v k ≤ Real.exp (2 * ∑ i ∈ P, v i) / (2:ℝ)^k := by
  apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) k)).mpr
  have he : elementary P v k * (2:ℝ)^k =
      ∑ t ∈ P.powersetCard k, ∏ i ∈ t, (2*v i) := by
    unfold elementary
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have hcard := (Finset.mem_powersetCard.mp ht).2
    simp only [Finset.prod_mul_distrib,Finset.prod_const,hcard]
    ring
  rw [he]
  calc
    _ ≤ ∑ t ∈ P.powerset, ∏ i ∈ t, (2*v i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp ht).1
      · intro t ht _
        exact Finset.prod_nonneg (fun i hi => mul_nonneg (by norm_num)
          (hv i (Finset.mem_powerset.mp ht hi)))
    _ = ∏ i ∈ P, (2*v i+1) := by
      simpa using (Finset.prod_add (fun i => 2*v i) (fun _ => (1:ℝ)) P).symm
    _ ≤ ∏ i ∈ P, Real.exp (2*v i) := by
      exact Finset.prod_le_prod₀ (fun i hi => by linarith [hv i hi])
        (fun i _ => Real.add_one_le_exp (2*v i))
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]

theorem elementary_source_scale (P : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ P, 0 ≤ v i) (L : ℝ) (hL : 1 ≤ L)
    (hS : (∑ i ∈ P, v i) ≤ 5*Real.log L) (k : ℕ) (hk : 1000*Real.log L ≤ k) :
    elementary P v k ≤ L ^ (-100:ℝ) := by
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h ⊢
    exact h
  have he : (2:ℝ)^k = Real.exp ((k:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ Real.exp (2*∑ i ∈ P, v i) / (2:ℝ)^k := elementary_le_exp P v hv k
    _ = Real.exp (2*∑ i ∈ P, v i - (k:ℝ)*Real.log 2) := by rw [he,Real.exp_sub]
    _ ≤ Real.exp ((-100)*Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k)
      nlinarith
    _ = _ := by rw [Real.rpow_def_of_pos hLp]; congr 1; ring

end OrdinaryCorrelations.SourceBonferroni

end

end OAI
