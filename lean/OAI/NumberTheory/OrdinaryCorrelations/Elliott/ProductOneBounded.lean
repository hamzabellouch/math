import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShiftedMultiplesCard
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ReciprocalRangeMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumDvdDilateComplex
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.SmoothCutoffExists

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
open scoped BigOperators ContDiff Topology
open scoped BigOperators Topology

namespace OrdinaryCorrelations.RawLower
open OrdinaryAnalyticCentering OrdinaryAnalyticCutoff

lemma product_oneBounded {f g : ℕ→ℂ} (hf : OneBounded f) (hg : OneBounded g) (m n : ℕ) :
    ‖f m*g n‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf m)).trans (hg n)

lemma cut_mul (phi : ℝ→ℝ) (B : ℝ) (d m : ℕ) :
    cut phi B d (d*m) = cut phi B d m := by
  exact cutoff_mul phi _ (fun p hp=>core_prime B (mem_filter.mp hp).1) _ d m
    (fun p hp=>(mem_filter.mp hp).2)

def dilatedTerm (phi : ℝ→ℝ) (B : ℝ) (f g : ℕ→ℂ) (h d m : ℕ) : ℂ :=
  f (d*m)*g (d*(m+h))*cut phi B d m*cut phi B d (m+h)

def corrSum (f g : ℕ→ℂ) (h N : ℕ) : ℂ := ∑ m∈Icc 1 N, f m*g (m+h)

lemma dilatedTerm_bound {f g : ℕ→ℂ} (hf : OneBounded f) (hg : OneBounded g)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1) (B : ℝ) (h d m : ℕ) :
    ‖dilatedTerm phi B f g h d m‖ ≤ 1 := by
  unfold dilatedTerm
  rw [norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (product_oneBounded hf hg _ _)).trans
      (norm_cutoff_le_one phi hb _ _ _))).trans (norm_cutoff_le_one phi hb _ _ _)

lemma raw_dilate (phi : ℝ→ℝ) (B : ℝ) (D : Finset ℕ) (a f g : ℕ→ℂ) (h : ℕ)
    (hd : ∀ d∈D, 0 < d) (X : ℝ) (hX : 0 ≤ X) :
    rawSum phi B D a f g h X =
      ∑ d∈D, a d*(divisorWeight B d:ℂ)*
        ∑ m∈Icc 1 ⌊X/d⌋₊, dilatedTerm phi B f g h d m := by
  unfold rawSum
  rw [sum_comm]
  apply sum_congr rfl
  intro d hdD
  have he (x:ℕ) : a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*
        cut phi B d x*cut phi B d (x+h*d)*(if d∣x then (1:ℂ) else 0) =
      if d∣x then a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*
        cut phi B d x*cut phi B d (x+h*d) else 0 := by
    split_ifs <;> ring
  simp only [he,←sum_filter]
  rw [sum_dvd_dilate_complex d (hd d hdD) X hX,mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [show d*m+h*d=d*(m+h) by ring,cut_mul,cut_mul]
  unfold dilatedTerm
  ring

lemma prefix_difference (u : ℕ→ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) {M N : ℕ} (hMN : M ≤ N) :
    ‖(∑ m∈Icc 1 M,u m)-(∑ m∈Icc 1 N,u m)‖ ≤ (N:ℝ)-(M:ℝ) := by
  rw [SourceRoughFourier.sum_Icc_one_eq_range,SourceRoughFourier.sum_Icc_one_eq_range,
    norm_sub_rev]
  rw [←sum_range_add_sum_Ico (fun n=>u (n+1)) hMN,add_sub_cancel_left]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _m∈Ico M N,(1:ℝ) := sum_le_sum (fun m hm=>hu _)
    _ = (N:ℝ)-(M:ℝ) := by simp [Nat.cast_sub hMN]

lemma length_bounds (τ H : ℝ) (hτ : 1 ≤ τ) (hH : 0 ≤ H) {d N : ℕ}
    (hd : 0 < d) (hHd : H ≤ d) (hdH : (d:ℝ) ≤ τ*H) :
    ⌊H*N/d⌋₊ ≤ N ∧ (N:ℝ)-(⌊H*N/d⌋₊:ℝ) ≤ (τ-1)*N+1 := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hratio : H*(N:ℝ)/d ≤ N := (div_le_iff₀ hd0).mpr (by nlinarith)
  have hnon : 0 ≤ H*(N:ℝ)/d := by positivity
  have hfloor := Nat.lt_floor_add_one (H*(N:ℝ)/d)
  have hlen : (2-τ)*(N:ℝ) ≤ H*N/d := by
    apply (le_div_iff₀ hd0).mpr
    have h1 : (τ-1)*(H*(N:ℝ)) ≥ 0 := mul_nonneg (sub_nonneg.mpr hτ) (mul_nonneg hH hN)
    have h2 : (τ-1)*((d:ℝ)-H)*(N:ℝ) ≥ 0 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hτ) (sub_nonneg.mpr hHd)) hN
    nlinarith [mul_le_mul_of_nonneg_right hdH hN]
  refine ⟨?_,by linarith⟩
  have hh := (Nat.floor_le hnon).trans hratio
  exact_mod_cast hh

lemma full_dilation_error (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    {B C₀ : ℝ} (hB : 1 ≤ B) {h d N : ℕ} (hd : 0 < d)
    (hcard : d.primeFactors.card ≤ J C₀ B) (hpr : d.primeFactors ⊆ core B∪center B)
    (hN : h ≤ N) :
    ‖(∑ m∈Icc 1 N,dilatedTerm phi B f g h d m) - (f d*g d)*corrSum f g h N‖ ≤
      6*(J C₀ B:ℝ)*(N:ℝ)/P₀ B+
        ∑ m∈Icc 1 N,‖cut phi B d m*cut phi B d (m+h)-1‖ := by
  let E : ℂ := ∑ m∈Icc 1 N,
    (f (d*m)*g (d*(m+h))-(f d*g d)*(f m*g (m+h)))*cut phi B d m*cut phi B d (m+h)
  let F : ℂ := ∑ m∈Icc 1 N, (f m*g (m+h))*(cut phi B d m*cut phi B d (m+h)-1)
  have hE : ‖E‖ ≤ 6*(J C₀ B:ℝ)*(N:ℝ)/P₀ B :=
    sum_product_error f g hf hg hmf hmg d h N (J C₀ B) hd hcard (P₀ B) (Real.exp_pos _)
      (fun p hp=>(prime_lower B hB (hpr hp)).le) hN phi hb _ _
  have hF : ‖F‖ ≤ ∑ m∈Icc 1 N,‖cut phi B d m*cut phi B d (m+h)-1‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro m hm
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (product_oneBounded hf hg _ _)
  have he : (∑ m∈Icc 1 N,dilatedTerm phi B f g h d m) - (f d*g d)*corrSum f g h N =
      E+(f d*g d)*F := by
    simp only [E,F,corrSum,mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    unfold dilatedTerm
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hq : ‖(f d*g d)*F‖ ≤ ‖F‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (product_oneBounded hf hg _ _)
  exact add_le_add hE (hq.trans hF)

lemma conjugate_product (z : ℂ) : star z*z = ((‖z‖^2:ℝ):ℂ) := by
  rw [mul_comm]
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.mul_conj' z

lemma weight_nonneg (B : ℝ) (d : ℕ) : 0 ≤ divisorWeight B d := by
  unfold divisorWeight A
  positivity

theorem raw_lower (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (h : ℕ) (C₀ γ τ T : ℝ) (hC : 0 ≤ C₀) (hγ : 0 < γ) (hτ : 1 ≤ τ)
    (hτγ : τ-1 ≤ γ/64) (hT : 0 < T) (hTγ : 32/T^2 ≤ γ/64)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hone : ∀ x, |x| ≤ T/2 → phi x = 1) :
    ∀ᶠ B : ℝ in atTop, ∀ H : ℝ, ∀ D : Finset ℕ, Admissible B C₀ τ H D →
      (∀ d∈D, 1/2 ≤ ‖f d*g d‖) → ∀ᶠ N : ℕ in atTop,
      γ*(N:ℝ) ≤ ‖corrSum f g h N‖ →
      (γ/8)*(N:ℝ)*H*(∑ d∈D, divisorWeight B d/d) ≤
        ‖rawSum phi B D (fun d=>star (f d*g d)) f g h (H*N)‖ := by
  have hJ : ∀ᶠ B : ℝ in atTop, 6*(J C₀ B:ℝ)/P₀ B ≤ γ/64 := by
    have ht : Tendsto (fun B:ℝ=>6*(J C₀ B:ℝ)/P₀ B) atTop (nhds 0) := by
      simpa only [mul_zero,mul_div_assoc] using (RawCutoff.defect_scale_tendsto C₀ hC).1.const_mul 6
    exact (ht.eventually (gt_mem_nhds (show 0 < γ/64 by positivity))).mono (fun _ hh=>hh.le)
  filter_upwards [hJ,RawCutoff.source_cutoff_error C₀ T hC hT phi hb hone h,
    eventually_ge_atTop (1:ℝ)] with B hJ hcut hB
  intro H D hD hmod
  have hH : 0 < H := by linarith [hD.1]
  have hd (d:ℕ) (hdD:d∈D) : 0 < d := by have := (hD.2.2 d hdD).2.2.1; omega
  have he : ∀ᶠ N:ℕ in atTop, ∀ d∈D,
      (∑ m∈Icc 1 N,‖cut phi B d m*cut phi B d (m+h)-1‖) ≤ (32/T^2+γ/64)*(N:ℝ) := by
    apply (eventually_all_finset D).mpr
    intro d hdD
    exact hcut d (hd d hdD) (hD.2.2 d hdD).2.2.2.2.2 (γ/64) (by positivity)
  have hsize : ∀ᶠ N:ℕ in atTop, 1 ≤ (γ/64)*(N:ℝ) := by
    have ht : Tendsto (fun N:ℕ=>(γ/64)*(N:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact ht.eventually_ge_atTop 1
  filter_upwards [he,hsize,eventually_ge_atTop h] with N hcutN hsize hN
  intro hbias
  let V : ℝ := ∑ d∈D, divisorWeight B d
  let K : ℝ := ∑ d∈D, ‖f d*g d‖^2*divisorWeight B d
  let U (d:ℕ) : ℂ := ∑ m∈Icc 1 ⌊H*(N:ℝ)/d⌋₊,dilatedTerm phi B f g h d m
  let S : ℂ := corrSum f g h N
  let R : ℂ := rawSum phi B D (fun d=>star (f d*g d)) f g h (H*N)
  have hV : 0 ≤ V := sum_nonneg (fun d hdD=>weight_nonneg B d)
  have hK : V/4 ≤ K := by
    rw [div_eq_mul_inv, sum_mul]
    apply sum_le_sum
    intro d hdD
    have hm := hmod d hdD
    have hq : 1/4 ≤ ‖f d*g d‖^2 := by nlinarith [norm_nonneg (f d*g d)]
    simpa only [one_div,mul_comm] using mul_le_mul_of_nonneg_right hq (weight_nonneg B d)
  have hK0 : 0 ≤ K := (div_nonneg hV (by norm_num)).trans hK
  have hper (d:ℕ) (hdD:d∈D) : ‖U d-(f d*g d)*S‖ ≤ (γ/8)*(N:ℝ) := by
    obtain ⟨hMN,hlen⟩ := length_bounds τ H hτ hH.le (hd d hdD)
      (hD.2.2 d hdD).2.2.2.1.le (hD.2.2 d hdD).2.2.2.2.1 (N:=N)
    have hpref := prefix_difference (dilatedTerm phi B f g h d)
      (dilatedTerm_bound hf hg phi hb B h d) hMN
    have hfull := full_dilation_error f g hf hg hmf hmg phi hb hB (hd d hdD)
      (hD.2.2 d hdD).2.2.2.2.2 (hD.2.2 d hdD).2.1 hN
    have hsplit := norm_sub_le_norm_sub_add_norm_sub (U d)
      (∑ m∈Icc 1 N,dilatedTerm phi B f g h d m) ((f d*g d)*S)
    have hJ' : 6*(J C₀ B:ℝ)*(N:ℝ)/P₀ B ≤ (γ/64)*(N:ℝ) := by
      simpa only [div_mul_eq_mul_div,mul_assoc] using mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg N)
    have hτ' := mul_le_mul_of_nonneg_right hτγ (Nat.cast_nonneg N)
    have hT' := mul_le_mul_of_nonneg_right hTγ (Nat.cast_nonneg N)
    have he := hcutN d hdD
    dsimp [U,S] at hsplit ⊢
    nlinarith
  have herr : ‖R-(K:ℂ)*S‖ ≤ (γ/8)*(N:ℝ)*V := by
    have hR : R-(K:ℂ)*S = ∑ d∈D, (divisorWeight B d:ℂ)*
        star (f d*g d)*(U d-(f d*g d)*S) := by
      dsimp [R]
      rw [raw_dilate phi B D _ f g h hd _ (by positivity)]
      simp only [K,Complex.ofReal_sum,Complex.ofReal_mul,sum_mul,←sum_sub_distrib]
      apply sum_congr rfl
      intro d hdD
      change star (f d*g d)*(divisorWeight B d:ℂ)*U d-
        ((‖f d*g d‖^2:ℝ):ℂ)*(divisorWeight B d:ℂ)*S = _
      rw [←conjugate_product]
      simp only [starRingEnd_apply]
      ring
    rw [hR]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ d∈D, divisorWeight B d*((γ/8)*(N:ℝ)) := by
        apply sum_le_sum
        intro d hdD
        rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (weight_nonneg B d),norm_star]
        apply mul_le_mul ?_ (hper d hdD) (norm_nonneg _) (weight_nonneg B d)
        exact mul_le_of_le_one_right (weight_nonneg B d) (product_oneBounded hf hg _ _)
      _ = _ := by rw [←sum_mul]; ring
  have hmain : (γ/8)*(N:ℝ)*V ≤ ‖R‖ := by
    have hl : (V/4)*(γ*(N:ℝ)) ≤ ‖(K:ℂ)*S‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK0]
      exact mul_le_mul hK hbias (by positivity) hK0
    have ht := norm_sub_le R (R-(K:ℂ)*S)
    rw [sub_sub_cancel] at ht
    nlinarith
  have hmass : H*(∑ d∈D,divisorWeight B d/d) ≤ V := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hdD
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd d hdD
    rw [←mul_div_assoc,div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_right (hD.2.2 d hdD).2.2.2.1.le (weight_nonneg B d)]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ (γ/8)*(N:ℝ))).trans hmain

end OrdinaryCorrelations.RawLower

end

end OAI
