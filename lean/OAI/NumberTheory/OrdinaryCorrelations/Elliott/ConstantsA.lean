import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Epsilon
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinaryTwistWidthBasic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Core
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CorePrime
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.OneAddSumLeProduct
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.WeightMeanOneLe

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators ContDiff
open Finset Filter Classical

namespace OrdinaryCorrelations.GraphBridge
open GraphKernel.PrimeSystem RawDivisorBin

lemma constants_A : OrdinaryAnalyticCentering.A = GraphKernel.PrimeSystem.A := by
  norm_num [OrdinaryAnalyticCentering.A,GraphKernel.PrimeSystem.A,kappa,GraphKernel.PrimeSystem.eta,GraphKernel.PrimeSystem.epsilon]

lemma center_eq_source {B : ℝ} (hB : 1 ≤ B) :
    OrdinaryAnalyticCentering.center B = SourcePrimeBands.centerPrimes B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hpow : B^(999999/1000000:ℝ) ≤ B := by
    convert Real.rpow_le_rpow_of_exponent_le hB (by norm_num : (999999/1000000:ℝ) ≤ 1) using 1
    rw [Real.rpow_one]
  ext p
  simp only [OrdinaryAnalyticCentering.center,SourcePrimeBands.centerPrimes,mem_filter,Finset.mem_Icc]
  have hp0 (hp : p.Prime) : (0:ℝ) < p := Nat.cast_pos.mpr hp.pos
  constructor
  · rintro ⟨⟨hp2,hpe⟩,hp,hl,hu⟩
    refine ⟨⟨hp2,?_⟩,hp,?_⟩
    · apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      apply (Real.log_le_iff_le_exp (hp0 hp)).mp
      convert hu using 1; norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon]
    · convert hl using 1; norm_num [SourcePrimeBands.epsilon]
  · rintro ⟨⟨hp2,hpe⟩,hp,hl⟩
    have hu : Real.log (p:ℝ) ≤ B^(999999/1000000:ℝ) := by
      apply (Real.log_le_iff_le_exp (hp0 hp)).mpr
      simpa only [SourcePrimeBands.eta,SourcePrimeBands.epsilon, show (1-(1/10000:ℝ)/100)=999999/1000000 by norm_num] using
        (Nat.le_floor_iff (Real.exp_pos _).le).mp hpe
    refine ⟨⟨hp2,?_⟩,hp,?_,hu⟩
    · apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      exact (Real.log_le_iff_le_exp (hp0 hp)).mp (hu.trans hpow)
    · convert hl using 1; norm_num [SourcePrimeBands.epsilon]

lemma source_primes {B : ℝ} (hB : 1 ≤ B) :
    (sourceSystem B).primes = OrdinaryAnalyticCentering.core B ∪ OrdinaryAnalyticCentering.center B := by
  rw [core_eq_source,center_eq_source hB]; rfl

lemma source_core (B : ℝ) : (sourceSystem B).core = OrdinaryAnalyticCentering.core B := (core_eq_source B).symm

lemma source_mean (B : ℝ) : (sourceSystem B).harmonicCore = OrdinaryAnalyticCentering.coreMean B := by
  rw [source_harmonicCore,OrdinaryAnalyticCentering.coreMean,core_eq_source]; rfl

lemma source_weight {B : ℝ} (hB : 1 ≤ B) : (sourceSystem B).weightMean = OrdinaryAnalyticCentering.L₀ B := by
  classical
  have he (p : (sourceSystem B).Index) : (sourceSystem B).amplitude p =
      if (p:ℕ)∈(sourceSystem B).core then GraphKernel.PrimeSystem.A else 1 := by
    unfold amplitude IsCore
    split_ifs <;> rfl
  simp only [weightMean,he]
  rw [←prod_subtype (sourceSystem B).primes (fun _ => Iff.rfl) (fun p : ℕ => 1+(if p∈(sourceSystem B).core then GraphKernel.PrimeSystem.A else 1)/(p:ℝ)),source_primes hB,source_core,
    prod_union (OrdinaryAnalyticCentering.core_center_disjoint B)]
  unfold OrdinaryAnalyticCentering.L₀
  congr 1
  · apply prod_congr rfl
    intro p hp
    rw [ite_eq_left hp,constants_A]
  · apply prod_congr rfl
    intro p hp
    rw [ite_eq_right (fun hc=>disjoint_left.mp (OrdinaryAnalyticCentering.core_center_disjoint B) hc hp),one_div]

def family {B C₀ τ H : ℝ} {D : Finset ℕ} (hB : 1 ≤ B)
    (hD : OrdinaryAnalyticCentering.Admissible B C₀ τ H D) : (sourceSystem B).DivisorFamily B τ C₀ where
  H := H
  members := D
  H_lower := hD.1
  H_upper := hD.2.1
  squarefree := fun d hd => (hD.2.2 d hd).1
  support := fun d hd => by rw [source_primes hB]; exact (hD.2.2 d hd).2.1
  greater_one := fun d hd => (hD.2.2 d hd).2.2.1
  lower := fun d hd => (hD.2.2 d hd).2.2.2.1
  upper := fun d hd => (hD.2.2 d hd).2.2.2.2.1
  omega := fun d hd => (hD.2.2 d hd).2.2.2.2.2

def cuts (B T : ℝ) (phi : ℝ→ℝ) (hμ : 0 < OrdinaryAnalyticCentering.coreMean B)
    (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hs : Function.support phi ⊆ Set.Icc (-T) T) : (sourceSystem B).Cutoffs T where
  value d r := phi (((sourceSystem B).cutoffCount d r-OrdinaryAnalyticCentering.coreMean B)/Real.sqrt (OrdinaryAnalyticCentering.coreMean B))
  nonneg d r := (hb _).1
  le_one d r := (hb _).2
  support d r h := by
    rw [source_mean] at h
    apply Function.notMem_support.mp
    intro hc
    have hlow := (hs hc).1
    have hsq := Real.sqrt_pos.mpr hμ
    have hl := (le_div_iff₀ hsq).mp hlow
    linarith

lemma source_core_sum {R : Type*} [AddCommMonoid R] (B : ℝ) (w : ℕ→R) :
    (∑ p : (sourceSystem B).CoreIndex,w (p.val:ℕ)) = ∑ p ∈ OrdinaryAnalyticCentering.core B,w p := by
  rw [core_eq_source,←sum_coe_sort (SourcePrimeBands.corePrimes B) w]
  exact (sourceCoreEquiv B).sum_comp (fun p=>w p.val)

lemma cutoffCount_integer (B : ℝ) (d n : ℕ) :
    (sourceSystem B).cutoffCount d ((sourceSystem B).restrictCore ((sourceSystem B).integerResidues n)) =
      OrdinaryTwistWidth.primeCount ((OrdinaryAnalyticCentering.core B).filter (fun p=>¬p∣d)) n := by
  have h := source_core_sum B (fun p=>if p∣n ∧ ¬p∣d then (1:ℕ) else 0)
  simpa only [cutoffCount,card_filter,restrictCore,integerResidues,Int.cast_natCast,
    ZMod.natCast_eq_zero_iff,OrdinaryTwistWidth.primeCount,filter_filter,sum_filter,
    ite_and,and_comm] using h

lemma cut_at_integer (B T : ℝ) (phi : ℝ→ℝ) (hμ : 0 < OrdinaryAnalyticCentering.coreMean B)
    (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hs : Function.support phi ⊆ Set.Icc (-T) T) (d n t : ℕ) :
    ((cuts B T phi hμ hb hs).value d ((sourceSystem B).shiftCore
      ((sourceSystem B).restrictCore ((sourceSystem B).integerResidues n)) t) : ℂ) =
      OrdinaryAnalyticCentering.cut phi B d (n+t) := by
  have hr : (sourceSystem B).shiftCore
      ((sourceSystem B).restrictCore ((sourceSystem B).integerResidues n)) t =
      (sourceSystem B).restrictCore ((sourceSystem B).integerResidues ((n+t:ℕ):ℤ)) := by
    funext p
    simp [shiftCore,restrictCore,integerResidues]
  change (phi (((sourceSystem B).cutoffCount d _-OrdinaryAnalyticCentering.coreMean B)/
    Real.sqrt (OrdinaryAnalyticCentering.coreMean B)) : ℂ) = _
  rw [hr,cutoffCount_integer]
  rfl
lemma prime_factor_integer {B : ℝ} (hB : 1 ≤ B) (d n : ℕ) :
    (((∏ p : (sourceSystem B).Index,
      if (p:ℕ)∣d then (sourceSystem B).divisorPrimeFactor ((sourceSystem B).integerResidues n) 0 p
      else 1) : ℝ) : ℂ) =
    (OrdinaryAnalyticCentering.divisorWeight B d:ℂ)*
      (if (∏ p∈(OrdinaryAnalyticCentering.core B).filter (fun p=>p∣d),p)∣n then (1:ℂ) else 0)*
      ∏ p∈(OrdinaryAnalyticCentering.center B).filter (fun p=>p∣d),
        ((if p∣n then (1:ℂ) else 0)-(1/4:ℂ)/(p:ℂ)) := by
  classical
  let u : ℕ→ℂ := fun p=>if p∣d then
    (if p∈OrdinaryAnalyticCentering.core B then
      (OrdinaryAnalyticCentering.A:ℂ)*(if p∣n then 1 else 0)
      else (if p∣n then 1 else 0)-(1/4:ℂ)/(p:ℂ)) else 1
  have hu : (((∏ p : (sourceSystem B).Index,
      if (p:ℕ)∣d then (sourceSystem B).divisorPrimeFactor ((sourceSystem B).integerResidues n) 0 p
      else 1) : ℝ) : ℂ) = ∏ p∈OrdinaryAnalyticCentering.core B∪OrdinaryAnalyticCentering.center B,u p := by
    rw [←source_primes hB,prod_subtype (sourceSystem B).primes (fun _=>Iff.rfl) u]
    push_cast
    apply prod_congr rfl
    intro p hp
    simp only [u,divisorPrimeFactor,IsCore,source_core,integerResidues,activity,Int.cast_zero,
      add_zero,Int.cast_natCast,ZMod.natCast_eq_zero_iff,SignedTrace.theta_value,←constants_A]
    split_ifs <;> simp_all
  rw [hu,prod_union (OrdinaryAnalyticCentering.core_center_disjoint B)]
  have hc : (∏ p∈OrdinaryAnalyticCentering.core B,u p) =
      (OrdinaryAnalyticCentering.divisorWeight B d:ℂ)*
      (if (∏ p∈(OrdinaryAnalyticCentering.core B).filter (fun p=>p∣d),p)∣n then (1:ℂ) else 0) := by
    calc
      _ = ∏ p∈(OrdinaryAnalyticCentering.core B).filter (fun p=>p∣d),
          ((OrdinaryAnalyticCentering.A:ℂ)*(if p∣n then 1 else 0)) := by
        rw [prod_filter]
        apply prod_congr rfl
        intro p hp
        simp [u,hp]
      _ = _ := by
        rw [prod_mul_distrib,prod_const,OrdinaryAnalyticCentering.prod_prime_indicator _
          (fun p hp=>OrdinaryAnalyticCentering.core_prime B (mem_filter.mp hp).1)]
        simp only [OrdinaryAnalyticCentering.divisorWeight,OrdinaryTwistWidth.primeCount,Complex.ofReal_pow]
  rw [hc]
  congr 1
  rw [prod_filter]
  apply prod_congr rfl
  intro p hp
  have hn : p∉OrdinaryAnalyticCentering.core B := fun h=>
    disjoint_left.mp (OrdinaryAnalyticCentering.core_center_disjoint B) h hp
  simp [u,hn]

lemma edge_at_integer {B : ℝ} (hB : 1 ≤ B) (T : ℝ) (phi : ℝ→ℝ)
    (hμ : 0 < OrdinaryAnalyticCentering.coreMean B)
    (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hs : Function.support phi ⊆ Set.Icc (-T) T) (d n t : ℕ) :
    ((sourceSystem B).divisorEdgeWeight (cuts B T phi hμ hb hs)
      ((sourceSystem B).integerResidues n) d 0 t : ℂ) =
      OrdinaryAnalyticCentering.kernel phi B d n (n+t) := by
  unfold divisorEdgeWeight OrdinaryAnalyticCentering.kernel
  simp only [Complex.ofReal_mul]
  rw [←Nat.cast_zero (R:=ℤ),cut_at_integer B T phi hμ hb hs d n 0,
    cut_at_integer B T phi hμ hb hs d n t]
  simp only [Nat.add_zero,Nat.cast_zero]
  rw [prime_factor_integer hB]
  ring

theorem centered_graph_bound (h : ℕ) (hh : 0 < h) (τ T C₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC : 0 ≤ C₀) (phi : ℝ→ℝ)
    (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hs : Function.support phi ⊆ Set.Icc (-T) T) :
    ∀ᶠ B : ℝ in atTop, ∀ H : ℝ, ∀ D : Finset ℕ,
      OrdinaryAnalyticCentering.Admissible B C₀ τ H D → ∀ a f g : ℕ→ℂ,
      (∀ d∈D, ‖a d‖ ≤ 1) → OneBounded f → OneBounded g → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ X : ℝ in atTop,
      ‖OrdinaryAnalyticCentering.centeredSum phi B D a f g h X‖/X ≤
        5*B^(-1-GraphKernel.PrimeSystem.eta/2:ℝ)*OrdinaryAnalyticCentering.L₀ B+δ := by
  filter_upwards [Sliding.source_divisorForm_bound h hh τ T C₀ hτ hτ2 hC,
    coreMass_tendsto.eventually_gt_atTop 0,eventually_ge_atTop (1:ℝ)] with B hg hμ hB
  have hμ' : 0 < OrdinaryAnalyticCentering.coreMean B := by
    simpa only [OrdinaryAnalyticCentering.coreMean,core_eq_source,SourcePrimeBands.coreMass] using hμ
  intro H D hD a f g ha hf hgg δ hδ
  have he (X:ℝ) : Sliding.divisorForm (family hB hD) h (cuts B T phi hμ' hb hs) a
      (fun n=>f n.toNat) (fun n=>g n.toNat) X =
      OrdinaryAnalyticCentering.centeredSum phi B D a f g h X := by
    unfold Sliding.divisorForm OrdinaryAnalyticCentering.centeredSum
    rw [sum_comm]
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [show (h:ℤ)*(d:ℤ)=((h*d:ℕ):ℤ) by simp,edge_at_integer hB]
    simp only [Int.toNat_natCast,←Nat.cast_add]
    ring
  simpa only [he,source_weight hB] using
    hg (family hB hD) (cuts B T phi hμ' hb hs) a ha (fun n=>f n.toNat) (fun n=>g n.toNat)
      (fun n=>hf n.toNat) (fun n=>hgg n.toNat) δ hδ

end OrdinaryCorrelations.GraphBridge

end

end OAI
