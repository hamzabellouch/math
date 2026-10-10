import Mathlib
import OAI.NumberTheory.PrimePackets.ZetaResidues

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma saturationIndex_le_packetScale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (saturationIndex M : ℝ) ≤ packetScale M := by
  have hD : (1:ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (fieldDiscriminant_one_le K)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hD

lemma nonzeroIdealWeight_eq_global {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) :
    nonzeroIdealWeight M I = globalIdealWeight M (nonzeroIntegralIdealUnit I) := rfl

 

theorem packetMeasure_box_moment_le_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → ℝ) {b c ε : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 < ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) :
    let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
    let z₀ : ℝ := ∏ i, |w i|
    (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ((Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)) *
      weightedIdealRealInterval M ((z₀+2*C*ε)*packetScale M) (4*C*ε*packetScale M) := by
  dsimp only
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let z₀ : ℝ := ∏ i, |w i|
  have hC : 0 < C := by dsimp [C]; positivity
  have hQ := packetScale_pos M
  rw [packetMeasure_siegel_unfolding M σ hn hodd _ (measurable_boxIndicator w ε)]
  rw [mul_assoc]
  apply _root_.mul_le_mul_right _ _
  unfold weightedIdealRealInterval
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro I
  have hN : 0 < (Ideal.absNorm I.1:ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2))
  have hz := div_pos hN hQ
  have H := productFiberIntegral_box_supported w hc hb hwlo hwhi hε.le hεc hε1 hz
  change productFiberIntegral (boxIndicator w ε) _ ≤
    if |(Ideal.absNorm I.1:ℝ)/packetScale M-z₀| ≤ C*ε then _ else 0 at H
  rw [nonzeroIdealWeight_eq_global]
  by_cases hs : |(Ideal.absNorm I.1:ℝ)/packetScale M-z₀| ≤ C*ε
  · have hh := abs_le.mp hs
    have hni : (z₀+2*C*ε)*packetScale M-4*C*ε*packetScale M < (Ideal.absNorm I.1:ℝ) ∧
        (Ideal.absNorm I.1:ℝ) ≤ (z₀+2*C*ε)*packetScale M := by
      have hlow : z₀-2*C*ε < (Ideal.absNorm I.1:ℝ)/packetScale M := by
        nlinarith [mul_pos hC hε]
      have hhigh : (Ideal.absNorm I.1:ℝ)/packetScale M ≤ z₀+2*C*ε := by
        nlinarith [mul_pos hC hε]
      constructor
      · have halg : (z₀+2*C*ε)*packetScale M-4*C*ε*packetScale M =
            (z₀-2*C*ε)*packetScale M := by ring
        rw [halg]
        exact (lt_div_iff₀ hQ).mp hlow
      · exact (div_le_iff₀ hQ).mp hhigh
    rw [ite_eq_left hni,mul_comm _ (globalIdealWeight M _)]
    apply _root_.mul_le_mul_right _ _
    simpa only [ite_eq_left hs] using H
  · have Hz : productFiberIntegral (boxIndicator w ε)
        ((Ideal.absNorm I.1:ℝ)/packetScale M) = 0 := by
      apply le_antisymm _ bot_le
      simpa only [ite_eq_right hs,ENNReal.bot_eq_zero] using H
    rw [Hz,mul_zero]
    exact bot_le

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

 

lemma packet_moment_normalization {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (B : ℝ≥0∞) (A : ℝ) (hA : 0 ≤ A) :
    (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ * B *
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (A*packetScale M*NumberField.dedekindZeta_residue K) = B*ENNReal.ofReal A := by
  have hD : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (fieldDiscriminant_one_le K))
  have hk := NumberField.dedekindZeta_residue_pos K
  have hQ := (packetScale_pos M).le
  have hqe : ENNReal.ofReal (packetScale M) =
      (saturationIndex M : ℝ≥0∞)*ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
    rw [packetScale,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul (mul_nonneg hA hQ),ENNReal.ofReal_mul hA,hqe]
  calc
    _ = ((ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
        (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))) *
        ((saturationIndex M : ℝ≥0∞)⁻¹ * (saturationIndex M : ℝ≥0∞)) * B * ENNReal.ofReal A := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hD)
        (ENNReal.ofReal_ne_zero_iff.mpr hk)) (ENNReal.mul_ne_top (by finiteness) (by finiteness)),
        ENNReal.inv_mul_cancel (by exact_mod_cast saturationIndex_ne_zero M) (by finiteness),
        one_mul,one_mul]

end PrimeDegreePackets

open Filter Set Topology
namespace PrimeDegreePackets

 

theorem box_interval_parameters {n : ℕ} (hn : 0 < n) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) :
    let C : ℝ := n*(b+1)^n
    let A₀ : ℝ := b^n+2*C+1
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      r ≤ c/2 ∧ r ≤ 1 ∧ 1 ≤ A₀ ∧ 0 < 4*C*r/A₀ ∧
      ∀ᶠ Q : ℝ in atTop, 0 < Q ∧
        ∀ w : Fin n → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          let z₀ := ∏ i, |w i|
          Q^(3/4:ℝ) ≤ (z₀+2*C*r)*Q ∧
          (z₀+2*C*r)*Q ≤ A₀*Q ∧
          (4*C*r/A₀)*((z₀+2*C*r)*Q) ≤ 4*C*r*Q ∧
          4*C*r*Q ≤ (z₀+2*C*r)*Q := by
  dsimp only
  let C : ℝ := n*(b+1)^n
  let A₀ : ℝ := b^n+2*C+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 1 ≤ A₀ := by
    have hbpow := pow_nonneg hb n
    dsimp only [A₀]
    linarith
  have hA0 : 0 < A₀ := by linarith
  refine ⟨min (c/2) (min 1 (c^n/(4*C))), by positivity, ?_⟩
  intro r hr hrr
  have hrc : r ≤ c/2 := (lt_min_iff.mp hrr).1.le
  have hr1 : r ≤ 1 := (lt_min_iff.mp (lt_min_iff.mp hrr).2).1.le
  have hrC : r < c^n/(4*C) := (lt_min_iff.mp (lt_min_iff.mp hrr).2).2
  have hCr : 4*C*r < c^n := by nlinarith [(lt_div_iff₀ (by positivity : 0 < 4*C)).mp hrC]
  refine ⟨hrc,hr1,hA,by positivity,?_⟩
  have Hratio : Tendsto (fun Q : ℝ => Q^(-1/4:ℝ)) atTop (𝓝 0) :=
    by simpa only [neg_div] using (tendsto_rpow_neg_atTop (y := (1/4:ℝ)) (by norm_num))
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Hratio.eventually_lt_const (pow_pos hc n)] with Q hQ hQr
  refine ⟨hQ,?_⟩
  intro w hwlo hwhi
  let z₀ : ℝ := ∏ i, |w i|
  have hzlo : c^n ≤ z₀ := by
    have H := Finset.prod_le_prod₀ (fun (_ : Fin n) (_ : _ ∈ Finset.univ) => hc.le)
      (fun i (_ : i ∈ Finset.univ) => hwlo i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using H
  have hzhi : z₀ ≤ b^n := by
    have H := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => abs_nonneg (w i))
      (fun i (_ : i ∈ Finset.univ) => hwhi i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using H
  have hsmall : Q^(3/4:ℝ) ≤ c^n*Q := by
    have He : Q^(3/4:ℝ) = Q^(-1/4:ℝ)*Q := by
      calc
        _ = Q^((-1/4:ℝ)+1) := by norm_num
        _ = _ := by rw [Real.rpow_add hQ,Real.rpow_one]
    rw [He]
    exact mul_le_mul_of_nonneg_right hQr.le hQ.le
  have hx : z₀+2*C*r ≤ A₀ := by dsimp only [A₀]; nlinarith
  refine ⟨?_,mul_le_mul_of_nonneg_right hx hQ.le,?_,?_⟩
  · exact hsmall.trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hC hr]) hQ.le)
  · have H := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 4*C*r/A₀)
    rw [div_mul_cancel₀ _ hA0.ne'] at H
    simpa only [C,A₀,z₀,mul_assoc] using mul_le_mul_of_nonneg_right H hQ.le
  · exact mul_le_mul_of_nonneg_right (by nlinarith) hQ.le

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma packet_box_constant_identity (d : ℕ) {c ε A : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (_hA : 0 ≤ A) :
    (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d) *
      ENNReal.ofReal (A*ε) = ENNReal.ofReal
        ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*A*ε^(d+1)) := by
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
  congr 1
  rw [show 4*ε/c=(4/c)*ε by ring,mul_pow,pow_succ]
  ring

 

theorem packetMeasure_box_moment_of_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → ℝ) {b c ε A : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 < ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) (hA : 0 ≤ A)
    (hcount : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε)*packetScale M)
      (4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (A*(4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M)*
        NumberField.dedekindZeta_residue K)) :
    (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
      ENNReal.ofReal ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*
        (A*4*((d+1:ℕ):ℝ)*(b+1)^(d+1))*ε^(d+1)) := by
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have H := packetMeasure_box_moment_le_count M σ hn hodd w hb hc hwlo hwhi hε hεc hε1
  dsimp only at H
  have hcount' : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*C*ε)*packetScale M) (4*C*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        ((A*4*C*ε)*packetScale M*NumberField.dedekindZeta_residue K) := by
    simpa only [C,mul_assoc] using hcount
  apply H.trans
  calc
    _ ≤ _ := mul_le_mul_right hcount' _
    _ = ((Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)) *
        ENNReal.ofReal (A*4*C*ε) := by
      rw [← mul_assoc]
      exact packet_moment_normalization M _ _ (by positivity)
    _ = _ := by
      rw [packet_box_constant_identity d hc hε.le (by positivity)]
      congr 1
      dsimp [C]
      ring

 

theorem packet_box_moment_bounded_discr (d : ℕ) (hodd : Odd (d+1))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ B r₀ : ℝ, 0 < B ∧ 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ N : ℕ,
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ w : Fin (d+1) → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*ε^(d+1)) := by
  obtain ⟨A,hA,Hcount⟩ := weightedIdeal_realInterval_bounded_discr (d+1) (by omega)
  obtain ⟨r₀,hr₀,Hpar⟩ := box_interval_parameters (n := d+1) (by omega) hb hc
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let A₀ : ℝ := b^(d+1)+2*C+1
  let B : ℝ := (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*(A*4*C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,r₀,hB,hr₀,?_⟩
  intro ε hε hεr N
  obtain ⟨hεc,hε1,hA₀,hη,Hε⟩ := Hpar ε hε hεr
  filter_upwards [Hε,Hcount N A₀ hA₀ (4*C*ε/A₀) hη] with Q hQ hcount
  intro K _ _ _ M σ hn hD hscale w hwlo hwhi
  obtain ⟨hxl,hxu,hrel,hyx⟩ := hQ.2 w hwlo hwhi
  have hq : (saturationIndex M:ℝ) ≤ Q := hscale ▸ saturationIndex_le_packetScale M
  have H := hcount K M (σ 0) hD hn hq _ _ hxl hxu hrel hyx
  rw [← hscale] at H
  have H' : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε)*packetScale M)
      (4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (A*(4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M)*
        NumberField.dedekindZeta_residue K) := by
    simpa only [C,mul_assoc] using H
  convert packetMeasure_box_moment_of_count M σ hn hodd w hb hc hwlo hwhi hε hεc hε1 hA.le H' using 1
  dsimp only [B,C]
  congr 1
  ring

end PrimeDegreePackets

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rightActionHomeomorph {n : ℕ} (g : G n) : X n ≃ₜ X n where
  toFun x := rightAction x g
  invFun x := rightAction x g⁻¹
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_rightAction g
  continuous_invFun := continuous_rightAction g⁻¹

 

theorem right_invariance_of_tendsto {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n))
    (hlim : Tendsto μ atTop (𝓝 ν)) (g : G n)
    (hinv : ∀ i, Measure.map (fun x => rightAction x g) (μ i : Measure (X n)) = μ i) :
    Measure.map (fun x => rightAction x g) (ν : Measure (X n)) = ν := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    μ ν hlim (continuous_rightAction g)
  have heq (i : ℕ) : (μ i).map (fun x => rightAction x g) = μ i := by
    apply Subtype.ext
    exact hinv i
  simp only [heq] at hmap
  have H := tendsto_nhds_unique hmap hlim
  exact congrArg (fun p : ProbabilityMeasure (X n) => (p : Measure (X n))) H

 

theorem tight_probability_subsequence {n : ℕ} (μ : ℕ → ProbabilityMeasure (X n))
    (htight : IsTightMeasureSet (Set.range (fun i => (μ i : Measure (X n))))) :
    ∃ ν : ProbabilityMeasure (X n), ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧ Tendsto (μ ∘ subsequence) atTop (𝓝 ν) := by
  have ht : IsTightMeasureSet
      {((ν : ProbabilityMeasure (X n)) : Measure (X n)) | ν ∈ Set.range μ} := by
    convert htight using 1
    ext ρ
    simp
  have hc := isCompact_closure_of_isTightMeasureSet ht
  obtain ⟨ν, -, subsequence, hsubsequence, hν⟩ := hc.tendsto_subseq
    (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν, subsequence, hsubsequence, hν⟩

 

lemma weakProbabilityConvergence_iff {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n)) :
    WeakProbabilityConvergence (fun i => (μ i : Measure (X n))) (ν : Measure (X n)) ↔ Tendsto μ atTop (𝓝 ν) := by
  simp only [WeakProbabilityConvergence]
  exact ⟨fun h => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr h.2.2,
    fun h => ⟨fun i => (μ i).property, ν.property,
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h⟩⟩

 

theorem tendsto_of_tight_of_unique_subsequential_limit {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n))
    (htight : IsTightMeasureSet (Set.range (fun i => (μ i : Measure (X n)))))
    (hunique : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ ξ : ProbabilityMeasure (X n),
      Tendsto (μ ∘ ψ) atTop (𝓝 ξ) → ξ = ν) :
    Tendsto μ atTop (𝓝 ν) := by
  have ht : IsTightMeasureSet
      {((ξ : ProbabilityMeasure (X n)) : Measure (X n)) | ξ ∈ Set.range μ} := by
    convert htight using 1
    ext ρ
    simp
  have hc := isCompact_closure_of_isTightMeasureSet ht
  apply hc.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun i => subset_closure (Set.mem_range_self i)))
  intro ξ _ hξ
  obtain ⟨ψ, hψ, hlim⟩ := hξ.tendsto_subseq
  exact hunique ψ hψ ξ hlim

 

theorem quotient_covering (n : ℕ) :
    IsCoveringMap (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) := by
  exact (isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroup
    (integralGroup n) (isDiscrete_iff_discreteTopology.mpr (by
      change DiscreteTopology (integralGroup n)
      infer_instance))
    (by intro a b; exact Quotient.eq''.trans QuotientGroup.rightRel_apply)).isCoveringMap

 

def matrixBall (n : ℕ) (r : ℝ) : Set (G n) :=
  {h | ∀ i j, |h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < r}

lemma matrixBall_isOpen (n : ℕ) (r : ℝ) : IsOpen (matrixBall n r) := by
  simp only [matrixBall, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact ((continuous_apply j).comp ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)).sub
    continuous_const |>.abs

lemma right_ball_isOpen {n : ℕ} (x : X n) (r : ℝ) :
    IsOpen ((fun h => rightAction x h) '' matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change IsOpen ((fun h => Quotient.mk _ (g*h)) '' matrixBall n r)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _
      ((Homeomorph.mulLeft g).isOpenMap _ (matrixBall_isOpen n r))

 

lemma vecMul_sub_coordinate_le {n : ℕ} (w : Fin n → ℝ) (h : G n)
    {r : ℝ} (hr : h ∈ matrixBall n r) (j : Fin n) :
    |(w ᵥ* h.1) j - w j| ≤ r * ∑ i, |w i| := by
  have he : (w ᵥ* h.1) j - w j =
      ∑ i, w i * (h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
    calc
      _ = (w ᵥ* (h.1 - (1 : Matrix (Fin n) (Fin n) ℝ))) j := by
        rw [Matrix.vecMul_sub, Matrix.vecMul_one]
        rfl
      _ = _ := rfl
  rw [he]
  calc
    _ ≤ ∑ i, |w i * (h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * r := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr i j).le (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

 

theorem exists_integer_row_no_zero_coordinate {n : ℕ} (g : G n) :
    ∃ z : Fin n → ℤ, ∀ j,
      ((fun i => (z i : ℝ)) ᵥ* g.1) j ≠ 0 := by
  let p (j : Fin n) : Polynomial ℝ := ∑ i : Fin n, Polynomial.monomial i.val (g.1 i j)
  have hcoeff (i j : Fin n) : (p j).coeff i.val = g.1 i j := by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      have hne : b.val ≠ i.val := fun e => hbi (Fin.ext e)
      simp only [hne, ite_false]
    · simp
  have hp (j : Fin n) : p j ≠ 0 := by
    intro hp
    have hz (i : Fin n) : g.1 i j = 0 := by rw [←hcoeff i j, hp]; simp
    have H := congrArg (fun q : G n => q.1 j j) (inv_mul_cancel g)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_apply, Matrix.one_apply_eq] at H
    simp only [hz, mul_zero, Finset.sum_const_zero] at H
    exact zero_ne_one H
  have hfin : (⋃ j, {t | (p j).IsRoot t}).Finite :=
    Set.finite_iUnion (fun j => Polynomial.finite_setOfPred_isRoot (hp j))
  have hinf : (Set.range (fun z : ℤ => (z : ℝ))).Infinite :=
    Set.infinite_range_of_injective Int.cast_injective
  obtain ⟨t,⟨N,rfl⟩, hN⟩ := hinf.exists_notMem_finite hfin
  refine ⟨fun i => N ^ i.val, fun j hj => hN ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change (p j).eval (N : ℝ) = 0
  simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Matrix.vecMul, dotProduct, Int.cast_pow, mul_comm] using hj

 

def vectorEnvelope (n k : ℕ) : Set (X n) :=
  {x | ∃ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
    ∃ z : Fin n → ℤ, ∀ j,
      (1:ℝ)/(k+1) < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
      |((fun i => (z i : ℝ)) ᵥ* g.1) j| < k+1}

lemma continuous_integer_row_coordinate {n : ℕ} (z : Fin n → ℤ) (j : Fin n) :
    Continuous (fun g : G n => ((fun i => (z i : ℝ)) ᵥ* g.1) j) := by
  change Continuous (fun g : G n => ∑ i, (z i : ℝ)*g.1 i j)
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  exact (continuous_apply j).comp ((continuous_apply i).comp
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)

lemma vectorEnvelope_isOpen (n k : ℕ) : IsOpen (vectorEnvelope n k) := by
  have heq : vectorEnvelope n k =
      ⋃ z : Fin n → ℤ,
        Quotient.mk (QuotientGroup.rightRel (integralGroup n)) ''
          {g : G n | ∀ j,
            (1:ℝ)/(k+1) < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
            |((fun i => (z i : ℝ)) ᵥ* g.1) j| < k+1} := by
    ext x
    simp only [vectorEnvelope, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨g,hg,z,hz⟩
      exact ⟨z,g,hz,hg⟩
    · rintro ⟨z,g,hz,hg⟩
      exact ⟨g,hg,z,hz⟩
  rw [heq]
  apply isOpen_iUnion
  intro z
  apply (quotient_covering n).isOpenMap
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt continuous_const (continuous_integer_row_coordinate z j).abs).inter
    (isOpen_lt (continuous_integer_row_coordinate z j).abs continuous_const)

lemma vectorEnvelope_mono {n j k : ℕ} (hjk : j ≤ k) :
    vectorEnvelope n j ⊆ vectorEnvelope n k := by
  rintro x ⟨g,hg,z,hz⟩
  refine ⟨g,hg,z,fun i => ?_⟩
  have hjkR : (j:ℝ)+1 ≤ k+1 := by exact_mod_cast Nat.succ_le_succ hjk
  refine ⟨lt_of_le_of_lt ?_ (hz i).1, (hz i).2.trans_le hjkR⟩
  exact one_div_le_one_div_of_le (by positivity) hjkR

lemma mem_vectorEnvelope {n : ℕ} (x : X n) : ∃ k, x ∈ vectorEnvelope n k := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z,hz⟩ := exists_integer_row_no_zero_coordinate g
    let w : Fin n → ℝ := (fun i => (z i : ℝ)) ᵥ* g.1
    obtain ⟨k,hk⟩ := exists_nat_gt (max ‖w‖ ‖fun j => 1 / |w j|‖)
    refine ⟨k,g,rfl,z,fun j => ?_⟩
    have habs : 0 < |w j| := abs_pos.mpr (hz j)
    have hw : |w j| < k+1 := by
      have H : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
      linarith [le_max_left ‖w‖ ‖fun j => 1 / |w j|‖]
    have hi : 1 / |w j| < k+1 := by
      have H : |1 / (|w j|)| ≤ ‖fun j => 1 / |w j|‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j => 1 / |w j|) j
      rw [abs_of_pos (one_div_pos.mpr habs)] at H
      linarith [le_max_right ‖w‖ ‖fun j => 1 / |w j|‖]
    refine ⟨?_,hw⟩
    apply (div_lt_iff₀ (show (0:ℝ) < k+1 by positivity)).mpr
    have H := (div_lt_iff₀ habs).mp hi
    nlinarith

 

theorem compact_uniform_vector_envelope {n : ℕ} {Ω : Set (X n)} (hΩ : IsCompact Ω) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ x ∈ Ω,
      ∃ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
        ∃ z : Fin n → ℤ, ∀ j,
          δ < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
          |((fun i => (z i : ℝ)) ᵥ* g.1) j| < B := by
  obtain ⟨s,hs⟩ := hΩ.elim_finite_subcover (vectorEnvelope n)
    (vectorEnvelope_isOpen n) (by
      intro x _
      obtain ⟨k,hk⟩ := mem_vectorEnvelope x
      exact Set.mem_iUnion.mpr ⟨k,hk⟩)
  let N := ∑ k ∈ s, k
  refine ⟨N+1,1/(N+1),by positivity,by positivity,?_⟩
  intro x hx
  obtain ⟨k,hks,hxk⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hkN : k ≤ N := Finset.single_le_sum (fun i _ => Nat.zero_le i) hks
  exact vectorEnvelope_mono hkN hxk

def orthoBox {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) : Set E :=
  {x | ∀ i, |u.repr x i| ≤ a i}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_preimage {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    orthoBox u a = (fun x => WithLp.ofLp (u.repr x)) ⁻¹' Set.Icc (-a) a := by
  ext x
  simp [orthoBox,abs_le,Pi.le_def,forall_and]

lemma orthoBox_volume {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    volume (orthoBox u a) = ∏ i, ENNReal.ofReal (2*a i) := by
  rw [orthoBox_preimage]
  have hp := (PiLp.volume_preserving_ofLp (Fin n)).comp u.measurePreserving_repr
  have H := hp.measure_preimage (measurableSet_Icc.nullMeasurableSet : NullMeasurableSet (Set.Icc (-a) a) volume)
  change volume ((WithLp.ofLp ∘ u.repr) ⁻¹' Set.Icc (-a) a) = _
  rw [H,Real.volume_Icc_pi]
  congr 1
  ext i
  simp [two_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_convex {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    Convex ℝ (orthoBox u a) := by
  rw [orthoBox_preimage]
  exact (convex_Icc (-a) a).linear_preimage
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toLinearMap.comp u.repr.toLinearMap)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_symmetric {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : -x ∈ orthoBox u a := by
  intro i
  simpa using hx i

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : ‖x‖ ≤ ∑ i, a i := by
  calc
    ‖x‖ = ‖∑ i, u.repr x i • u i‖ := by rw [u.sum_repr]
    _ ≤ ∑ i, ‖u.repr x i • u i‖ := norm_sum_le _ _
    _ = ∑ i, |u.repr x i| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hx i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le_of_zero_first {n : ℕ} (u : OrthonormalBasis (Fin (n+1)) ℝ E)
    (a : Fin (n+1) → ℝ) {x : E} (hx : x ∈ orthoBox u a) (hzero : u.repr x 0 = 0) :
    ‖x‖ ≤ ∑ i : Fin n, a i.succ := by
  calc
    ‖x‖ = ‖∑ i : Fin n, u.repr x i.succ • u i.succ‖ := by
      have H := u.sum_repr x
      rw [Fin.sum_univ_succ,hzero,zero_smul,zero_add] at H
      exact congrArg norm H.symm
    _ ≤ ∑ i : Fin n, ‖u.repr x i.succ • u i.succ‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |u.repr x i.succ| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, a i.succ := Finset.sum_le_sum (fun i _ => hx i.succ)

omit [MeasurableSpace E] [BorelSpace E] in
 

lemma exists_orthonormal_first_perp {n : ℕ} (hdim : finrank ℝ E = n+1)
    (W : Submodule ℝ E) (hW : W ≠ ⊤) :
    ∃ u : OrthonormalBasis (Fin (n+1)) ℝ E, ∀ x ∈ W, u.repr x 0 = 0 := by
  have hperp : Wᗮ ≠ ⊥ := fun h => hW (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w,norm_smul,hv0]
  have hwW : w ∈ Wᗮ := Wᗮ.smul_mem _ hv
  have H : Orthonormal ℝ (({0} : Set (Fin (n+1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    subst j
    simp [hw]
  obtain ⟨u,hu⟩ := H.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  refine ⟨u,?_⟩
  intro x hx
  rw [u.repr_apply_apply,hu 0 (by simp)]
  exact (real_inner_comm _ _).trans ((Submodule.mem_orthogonal _ _).mp hwW x hx)

 

theorem bounded_vector_outside_subspace {n : ℕ} (hdim : finrank ℝ E = n+1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) = 1 →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ε ≤ ‖v‖) →
      ∀ W : Submodule ℝ E, W ≠ ⊤ →
        ∃ v ∈ Submodule.span ℤ (Set.range b), v ∉ W ∧ ‖v‖ ≤ B := by
  let s : ℝ := min 1 (ε / (2*(n+1)))
  have hs : 0 < s := lt_min zero_lt_one (div_pos hε (by positivity))
  let R : ℝ := 2/s^n
  have hR : 0 < R := div_pos (by norm_num) (pow_pos hs _)
  refine ⟨R+(n:ℝ)*s,by positivity,?_⟩
  intro b hb hshort W hW
  obtain ⟨u,hu⟩ := exists_orthonormal_first_perp hdim W hW
  let a : Fin (n+1) → ℝ := Fin.cons R (fun _ => s)
  have hvol : (volume (ZSpan.fundamentalDomain b))*2^(finrank ℝ E) <
      volume (orthoBox u a) := by
    rw [hb,one_mul,hdim,orthoBox_volume,Fin.prod_univ_succ]
    simp only [a,Fin.cons_zero,Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*s),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]
    have H : (2*R)*(2*s)^n = (2:ℝ)^(n+1)*2 := by
      dsimp [R]
      rw [mul_pow,pow_succ]
      field_simp
    rw [H,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    simpa only [mul_one] using ENNReal.mul_lt_mul_right
      (by positivity : (2:ℝ≥0∞)^(n+1) ≠ 0) (by finiteness) (by norm_num : (1:ℝ≥0∞) < 2)
  let L := Submodule.span ℤ (Set.range b)
  have : Countable L := inferInstance
  obtain ⟨v,hv0,hv⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup)
    (ZSpan.isAddFundamentalDomain b volume) (fun x hx => orthoBox_symmetric u a hx)
    (orthoBox_convex u a) hvol
  have hvE : (v : E) ≠ 0 := by exact_mod_cast hv0
  refine ⟨v,v.property,?_,?_⟩
  · intro hvW
    have H := orthoBox_norm_le_of_zero_first u a hv (hu _ hvW)
    simp only [a,Fin.cons_succ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] at H
    have hsε : s ≤ ε/(2*(n+1)) := min_le_right _ _
    have Hs : (n:ℝ)*s < ε := by
      have Hn : (n:ℝ)*s ≤ ((n:ℝ)+1)*s := by nlinarith
      have Hs : ((n:ℝ)+1)*s ≤ ε/2 := by
        have := (le_div_iff₀ (by positivity : 0 < 2*((n:ℝ)+1))).mp hsε
        nlinarith
      linarith
    exact (hshort v v.property hvE).not_gt (lt_of_le_of_lt H Hs)
  · have H := orthoBox_norm_le u a hv
    simpa [a,Fin.sum_univ_succ] using H

 

theorem bounded_real_basis_in_lattice {n : ℕ} (hdim : finrank ℝ E = n+1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) = 1 →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ε ≤ ‖v‖) →
      ∃ c : Basis (Fin (n+1)) ℝ E,
        ∀ i, c i ∈ Submodule.span ℤ (Set.range b) ∧ ‖c i‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := bounded_vector_outside_subspace hdim ε hε
  refine ⟨B,hB,?_⟩
  intro b hb hshort
  let S : Set E := {x | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ B}
  have hsp : Submodule.span ℝ S = ⊤ := by
    by_contra hne
    obtain ⟨v,hv,hvW,hvB⟩ := H b hb hshort (Submodule.span ℝ S) hne
    exact hvW (Submodule.subset_span (show v ∈ S from ⟨hv,hvB⟩))
  obtain ⟨T,hTS,hTspan,hTind⟩ := exists_linearIndependent ℝ S
  have hTtop : Submodule.span ℝ T = ⊤ := hTspan.trans hsp
  let c₀ : Basis T ℝ E := Basis.mk hTind (by
    rw [Subtype.range_coe_subtype]
    change ⊤ ≤ Submodule.span ℝ T
    rw [hTtop])
  have : Finite T := hTind.finite
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = n+1 := (finrank_eq_card_basis c₀).symm.trans hdim
  let e : T ≃ Fin (n+1) := Fintype.equivFinOfCardEq hcard
  refine ⟨c₀.reindex e,?_⟩
  intro i
  have H := hTS (e.symm i).property
  simpa [c₀,Basis.coe_reindex,S] using H

open scoped Matrix
open Matrix

def rowBasis {n : ℕ} (g : G n) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (Matrix.SpecialLinearGroup.toLin' g.transpose)

@[simp] lemma rowBasis_apply {n : ℕ} (g : G n) (i j : Fin n) :
    rowBasis g i j = g.1 i j := by
  simp [rowBasis,Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply,
    Matrix.mulVec,dotProduct,Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_apply,Pi.single_apply]

def euclideanRowBasis {n : ℕ} (g : G n) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (rowBasis g).map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toLinearEquiv

@[simp] lemma euclideanRowBasis_apply {n : ℕ} (g : G n) (i j : Fin n) :
    (euclideanRowBasis g i).ofLp j = g.1 i j := by
  simp [euclideanRowBasis]

lemma euclideanRowBasis_volume {n : ℕ} (g : G n) :
    volume (ZSpan.fundamentalDomain (euclideanRowBasis g)) = 1 := by
  let u := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hi : u.toLinearEquiv '' ZSpan.fundamentalDomain (euclideanRowBasis g) =
      ZSpan.fundamentalDomain (rowBasis g) := by
    rw [ZSpan.map_fundamentalDomain]
    congr 1
  have hp : u ⁻¹' ZSpan.fundamentalDomain (rowBasis g) =
      ZSpan.fundamentalDomain (euclideanRowBasis g) := by
    rw [← hi]
    exact Set.preimage_image_eq _ u.injective
  have hm := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (ZSpan.fundamentalDomain_measurableSet (rowBasis g)).nullMeasurableSet
  change volume (u ⁻¹' ZSpan.fundamentalDomain (rowBasis g)) = _ at hm
  rw [hp,ZSpan.volume_fundamentalDomain] at hm
  have hr : Matrix.of (rowBasis g) = g.1 := by ext i j; exact rowBasis_apply g i j
  simpa [hr,g.2] using hm

lemma sum_euclideanRowBasis {n : ℕ} (g : G n) (z : Fin n → ℤ) :
    ∑ i, z i • euclideanRowBasis g i =
      WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1) := by
  ext j
  simp [Matrix.vecMul,dotProduct,← Int.cast_smul_eq_zsmul ℝ]

 

theorem bounded_independent_rows (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ g : G (n+1),
      (∀ z : Fin (n+1) → ℤ, z ≠ 0 →
        ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖) →
      ∃ Z : Matrix (Fin (n+1)) (Fin (n+1)) ℤ,
        Z.det ≠ 0 ∧ ∀ i j, |((Z.map (Int.castRingHom ℝ))*g.1) i j| ≤ B := by
  obtain ⟨B,hB,H⟩ := bounded_real_basis_in_lattice
    (E := EuclideanSpace ℝ (Fin (n+1))) (n := n) (by simp) ε hε
  refine ⟨B,hB,?_⟩
  intro g hg
  have hshort : ∀ v ∈ Submodule.span ℤ (Set.range (euclideanRowBasis g)),
      v ≠ 0 → ε ≤ ‖v‖ := by
    intro v hv hv0
    obtain ⟨z,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
    have hz : z ≠ 0 := by intro hz; simp [hz] at hv0
    rw [sum_euclideanRowBasis]
    exact hg z hz
  obtain ⟨c,hc⟩ := H (euclideanRowBasis g) (euclideanRowBasis_volume g) hshort
  choose Z hZ using (fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hc i).1)
  let V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j => (c i).ofLp j
  have hV : V = (Matrix.of Z).map (Int.castRingHom ℝ)*g.1 := by
    ext i j
    have H := congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v.ofLp j) (hZ i)
    rw [sum_euclideanRowBasis] at H
    exact H.symm
  have hdetV : V.det ≠ 0 := by
    let c' := c.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).toLinearEquiv
    have H := ((Pi.basisFun ℝ (Fin (n+1))).isUnit_det c').ne_zero
    have he : (Pi.basisFun ℝ (Fin (n+1))).det c' = V.det := by
      rw [Basis.det_apply,← Matrix.det_transpose]
      rfl
    rwa [he] at H
  refine ⟨Matrix.of Z,?_,?_⟩
  · intro hz
    apply hdetV
    rw [hV,Matrix.det_mul]
    have H : ((Matrix.of Z).map (Int.castRingHom ℝ)).det = ((Matrix.of Z).det : ℝ) :=
      (Int.cast_det (Matrix.of Z)).symm
    rw [H,hz]
    simp
  · intro i j
    rw [← hV]
    exact (PiLp.norm_apply_le (c i) j).trans (hc i).2

 

def coordinateMod (n m : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod m) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp [zsmul_eq_mul]

lemma coordinateMod_ker {n m : ℕ} (v : Fin n → ℤ) :
    v ∈ (coordinateMod n m).ker ↔ ∃ w : Fin n → ℤ, v = (m:ℤ) • w := by
  change ((fun i => (v i : ZMod m)) = 0) ↔ _
  constructor
  · intro hv
    have hd (i : Fin n) : (m:ℤ) ∣ v i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hv i)
    choose w hw using hd
    exact ⟨w,funext hw⟩
  · rintro ⟨w,rfl⟩
    ext i
    simp

lemma finite_integral_submodules_above_mod (n m : ℕ) (hm : m ≠ 0) :
    {L : Submodule ℤ (Fin n → ℤ) | (coordinateMod n m).ker ≤ L}.Finite := by
  let : NeZero m := ⟨hm⟩
  let F := coordinateMod n m
  have : Finite {L : Submodule ℤ (Fin n → ℤ) // F.ker ≤ L} :=
    Finite.of_injective (fun L : {L : Submodule ℤ (Fin n → ℤ) // F.ker ≤ L} => L.val.map F)
      (by
        intro L M h
        apply Subtype.ext
        have H := congrArg (Submodule.comap F) h
        simpa only [Submodule.comap_map_eq,sup_eq_left.mpr L.property,
          sup_eq_left.mpr M.property] using H)
  exact Set.finite_coe_iff.mp this

 

def columnModule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.range A.mulVecLin

lemma det_smul_mem_columnModule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : A.det • v ∈ columnModule A := by
  refine ⟨A.adjugate.mulVec v,?_⟩
  change A.mulVec (A.adjugate.mulVec v) = _
  rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]

lemma coordinateMod_ker_le_columnModule {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) (hN : A.det.natAbs ≤ N) :
    (coordinateMod n (N.factorial)).ker ≤ columnModule A := by
  have hd : A.det ∣ (N.factorial:ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa using Nat.dvd_factorial (Int.natAbs_pos.mpr hA) hN)
  obtain ⟨k,hk⟩ := hd
  intro v hv
  obtain ⟨w,rfl⟩ := (coordinateMod_ker v).mp hv
  rw [hk,mul_smul]
  exact det_smul_mem_columnModule A (k • w)

 

theorem finite_bounded_column_modules (n N : ℕ) :
    {L : Submodule ℤ (Fin n → ℤ) | ∃ A : Matrix (Fin n) (Fin n) ℤ,
      A.det ≠ 0 ∧ A.det.natAbs ≤ N ∧ columnModule A = L}.Finite := by
  apply (finite_integral_submodules_above_mod n N.factorial (Nat.factorial_ne_zero N)).subset
  rintro L ⟨A,hA,hN,rfl⟩
  exact coordinateMod_ker_le_columnModule A hA hN

lemma exists_int_matrix_of_columnModule_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (hAB : columnModule A ≤ columnModule B) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, A = B*C := by
  have hcol (j : Fin n) : (fun i => A i j) ∈ columnModule A := by
    refine ⟨Pi.single j 1,?_⟩
    change A.mulVec (Pi.single j 1) = _
    ext i
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  have H (j : Fin n) : ∃ v : Fin n → ℤ, B.mulVec v = fun i => A i j := hAB (hcol j)
  choose C hC using H
  refine ⟨Matrix.transpose C,?_⟩
  ext i j
  have H := congrFun (hC j) i
  exact H.symm

 

lemma exists_SL_of_columnModule_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : 0 < A.det) (hB : 0 < B.det) (hAB : columnModule A = columnModule B) :
    ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  obtain ⟨C,hC⟩ := exists_int_matrix_of_columnModule_le A B hAB.le
  obtain ⟨D,hD⟩ := exists_int_matrix_of_columnModule_le B A hAB.symm.le
  have hdC : A.det = B.det*C.det := by rw [hC,Matrix.det_mul]
  have hdD : B.det = A.det*D.det := by rw [hD,Matrix.det_mul]
  have hCD : C.det*D.det = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hB)
    linear_combination -(hdC*D.det+hdD)
  have hu : IsUnit C.det := isUnit_iff_dvd_one.mpr ⟨D.det,hCD.symm⟩
  have hC1 : C.det = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · rw [h] at hdC
      linarith
  exact ⟨⟨C,hC1⟩,hC⟩

 

theorem finite_bounded_matrix_representatives (n N : ℕ) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℤ),
      (∀ B ∈ s, 0 < B.det) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℤ, 0 < A.det → A.det.natAbs ≤ N →
        ∃ B ∈ s, ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  classical
  let S : Set (Submodule ℤ (Fin n → ℤ)) :=
    {L | ∃ A : Matrix (Fin n) (Fin n) ℤ, 0 < A.det ∧ A.det.natAbs ≤ N ∧ columnModule A = L}
  have hS : S.Finite := (finite_bounded_column_modules n N).subset (by
    rintro L ⟨A,hA,hN,hL⟩
    exact ⟨A,ne_of_gt hA,hN,hL⟩)
  let : Fintype S := hS.fintype
  choose B hB using (fun L : S => L.property)
  refine ⟨Finset.univ.image B,?_,?_⟩
  · intro A hA
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hA
    exact (hB L).1
  · intro A hA hN
    let L : S := ⟨columnModule A,⟨A,hA,hN,rfl⟩⟩
    refine ⟨B L,Finset.mem_image.mpr ⟨L,Finset.mem_univ _,rfl⟩,?_⟩
    exact exists_SL_of_columnModule_eq A (B L) hA (hB L).1 (hB L).2.2.symm

lemma exists_SL_of_signed_columnModule_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (_hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hsign : 0 < A.det ↔ 0 < B.det) (hAB : columnModule A = columnModule B) :
    ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  obtain ⟨C,hC⟩ := exists_int_matrix_of_columnModule_le A B hAB.le
  obtain ⟨D,hD⟩ := exists_int_matrix_of_columnModule_le B A hAB.symm.le
  have hdC : A.det = B.det*C.det := by rw [hC,Matrix.det_mul]
  have hdD : B.det = A.det*D.det := by rw [hD,Matrix.det_mul]
  have hCD : C.det*D.det = 1 := by
    apply mul_left_cancel₀ hB
    linear_combination -(hdC*D.det+hdD)
  have hu : IsUnit C.det := isUnit_iff_dvd_one.mpr ⟨D.det,hCD.symm⟩
  have hC1 : C.det = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · rw [h] at hdC
      by_cases hpos : 0 < A.det
      · have := hsign.mp hpos
        omega
      · have := mt hsign.mpr hpos
        omega
  exact ⟨⟨C,hC1⟩,hC⟩

 

theorem finite_bounded_nonsingular_matrix_representatives (n N : ℕ) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℤ),
      (∀ B ∈ s, B.det ≠ 0) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℤ, A.det ≠ 0 → A.det.natAbs ≤ N →
        ∃ B ∈ s, ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  classical
  let S : Set (Submodule ℤ (Fin n → ℤ) × Bool) :=
    {L | ∃ A : Matrix (Fin n) (Fin n) ℤ, A.det ≠ 0 ∧ A.det.natAbs ≤ N ∧
      columnModule A = L.1 ∧ decide (0 < A.det) = L.2}
  have hS : S.Finite :=
    ((finite_bounded_column_modules n N).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset (by
      rintro ⟨L,b⟩ ⟨A,hA,hN,hL,hb⟩
      exact ⟨⟨A,hA,hN,hL⟩,Set.mem_univ _⟩)
  let : Fintype S := hS.fintype
  choose B hB using (fun L : S => L.property)
  refine ⟨Finset.univ.image B,?_,?_⟩
  · intro A hA
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hA
    exact (hB L).1
  · intro A hA hN
    let L : S := ⟨(columnModule A,decide (0 < A.det)),⟨A,hA,hN,rfl,rfl⟩⟩
    refine ⟨B L,Finset.mem_image.mpr ⟨L,Finset.mem_univ _,rfl⟩,?_⟩
    apply exists_SL_of_signed_columnModule_eq A (B L) hA (hB L).1
    · have H := (hB L).2.2.2
      change decide (0 < (B L).det) = decide (0 < A.det) at H
      by_cases hpos : 0 < A.det
      · simp only [hpos,decide_true] at H
        exact iff_of_true hpos (of_decide_eq_true H)
      · simp only [hpos,decide_false] at H
        exact iff_of_false hpos (of_decide_eq_false H)
    · exact (hB L).2.2.1.symm

 

theorem bounded_SL_representatives (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ), IsCompact K ∧
      ∀ g : G (n+1),
        (∀ z : Fin (n+1) → ℤ, z ≠ 0 →
          ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖) →
        ∃ C : Matrix.SpecialLinearGroup (Fin (n+1)) ℤ,
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g).1 ∈ K := by
  classical
  obtain ⟨B,hB,H⟩ := bounded_independent_rows n ε hε
  let K₀ : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
    (Set.Icc (fun _ _ => -B) (fun _ _ => B) : Set (Fin (n+1) → Fin (n+1) → ℝ))
  have hK₀ : IsCompact K₀ := isCompact_Icc (α := Fin (n+1) → Fin (n+1) → ℝ)
  obtain ⟨D,hD⟩ := hK₀.bddAbove_image (continuous_id.matrix_det.abs.continuousOn)
  obtain ⟨N,hN⟩ := exists_nat_gt D
  obtain ⟨s,hs,Hs⟩ := finite_bounded_nonsingular_matrix_representatives (n+1) N
  let K : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
    ⋃ A ∈ (s : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℤ)),
      (fun V => (A.map (Int.castRingHom ℝ))⁻¹ * V) '' K₀
  have hK : IsCompact K := s.finite_toSet.isCompact_biUnion (fun A _ =>
    hK₀.image (continuous_const.matrix_mul continuous_id))
  refine ⟨K,hK,?_⟩
  intro g hg
  obtain ⟨Z,hZ,hZB⟩ := H g hg
  have hV : Z.map (Int.castRingHom ℝ)*g.1 ∈ K₀ := by
    show (∀ i j, -B ≤ (Z.map (Int.castRingHom ℝ)*g.1) i j) ∧
      (∀ i j, (Z.map (Int.castRingHom ℝ)*g.1) i j ≤ B)
    exact ⟨fun i j => (abs_le.mp (hZB i j)).1,fun i j => (abs_le.mp (hZB i j)).2⟩
  have hZN : Z.det.natAbs ≤ N := by
    have hd := hD (Set.mem_image_of_mem (fun V => |V.det|) hV)
    have he : (Z.map (Int.castRingHom ℝ)*g.1).det = (Z.det : ℝ) := by
      rw [Matrix.det_mul,g.2,mul_one]
      exact (Int.cast_det Z).symm
    rw [he] at hd
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_natAbs,Int.cast_abs]
    exact hd.trans hN.le
  obtain ⟨A,hA,C,hC⟩ := Hs Z hZ hZN
  refine ⟨C,?_⟩
  apply Set.mem_iUnion_of_mem A
  apply Set.mem_iUnion_of_mem hA
  refine ⟨Z.map (Int.castRingHom ℝ)*g.1,hV,?_⟩
  have hA0 : IsUnit (A.map (Int.castRingHom ℝ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) from (Int.cast_det A).symm]
    exact_mod_cast hs A hA
  have hmap : Z.map (Int.castRingHom ℝ) =
      A.map (Int.castRingHom ℝ) * C.1.map (Int.castRingHom ℝ) := by
    rw [hC]
    exact Matrix.map_mul
  change (A.map (Int.castRingHom ℝ))⁻¹ * (Z.map (Int.castRingHom ℝ)*g.1) =
    C.1.map (Int.castRingHom ℝ)*g.1
  rw [hmap,← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hA0,
    Matrix.one_mul]

open TopologicalSpace
open scoped Topology

def thickLattices (n : ℕ) (ε : ℝ) : Set (X n) :=
  {x | ∀ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x →
    ∀ z : Fin n → ℤ, z ≠ 0 → ε ≤ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖}

lemma continuous_integer_row (n : ℕ) (z : Fin n → ℤ) :
    Continuous (fun g : G n => (fun i => (z i : ℝ)) ᵥ* g.1) := by
  apply continuous_pi
  intro j
  change Continuous (fun g : G n => ∑ i, (z i : ℝ)*g.1 i j)
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)))

lemma thickLattices_isClosed (n : ℕ) (ε : ℝ) : IsClosed (thickLattices n ε) := by
  classical
  have he : (thickLattices n ε)ᶜ =
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) ''
        {g : G n | ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} := by
    ext x
    simp [thickLattices,not_forall,not_le,and_comm]
  apply isOpen_compl_iff.mp
  rw [he]
  apply (quotient_covering n).isOpenMap
  have he' : {g : G n | ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} =
      ⋃ (z : Fin n → ℤ) (_ : z ≠ 0), {g : G n | ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} := by
    ext g; simp
  rw [he']
  exact isOpen_iUnion (fun z => isOpen_iUnion (fun _ =>
    isOpen_lt (continuous_integer_row n z).norm continuous_const))

 

theorem mahler_compact (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsCompact (thickLattices (n+1) ε) := by
  obtain ⟨K,hK,H⟩ := bounded_SL_representatives n ε hε
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set (G (n+1))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK
  have himage := hpre.image
    (continuous_quotient_mk' : Continuous
      (Quotient.mk (QuotientGroup.rightRel (integralGroup (n+1)))))
  apply himage.of_isClosed_subset (thickLattices_isClosed (n+1) ε)
  intro x hx
  induction x using Quotient.inductionOn with
  | h g =>
    have hshort : ∀ z : Fin (n+1) → ℤ, z ≠ 0 →
        ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖ := by
      intro z hz
      refine (hx g rfl z hz).trans ?_
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact PiLp.norm_apply_le (WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)) i
    obtain ⟨C,hC⟩ := H g hshort
    refine ⟨(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g,hC,?_⟩
    apply Quotient.sound
    change (QuotientGroup.rightRel (integralGroup (n+1)))
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g) g
    rw [QuotientGroup.rightRel_apply]
    refine ⟨C⁻¹, ?_⟩
    simp

def packetSupport {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) : Set (X (d+1)) :=
  ⋃ O : packetOrbits M σ, O.1

lemma packetSupport_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : IsCompact (packetSupport M σ) := by
  let : Fintype (packetOrbits M σ) := (packetOrbits_finite M σ hn hodd).fintype
  exact isCompact_iUnion (fun O => packetOrbit_isCompact hn hodd O)

lemma orbitProbability_compl_range {d : ℕ} (x : X (d+1))
    {s : Set (X (d+1))} (hs : MeasurableSet s) (hr : diagonalOrbit x ⊆ s) :
    orbitProbability x sᶜ = 0 := by
  rw [orbitProbability,Measure.smul_apply,orbitalHaar]
  split_ifs
  · rw [Measure.map_apply (continuous_orbitMap x).measurable hs.compl]
    have H : orbitMap x ⁻¹' sᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hu (hr ⟨u,rfl⟩)
    rw [H,measure_empty,smul_zero]
  · simp

 

theorem packetMeasure_compl_support {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : packetMeasure M σ (packetSupport M σ)ᶜ = 0 := by
  have hs := (packetSupport_isCompact M σ hn hodd).isClosed.measurableSet
  rw [packetMeasure,Measure.smul_apply,Measure.sum_apply _ hs.compl]
  have H (O : packetOrbits M σ) : orbitProbability (orbitBasepoint O) (packetSupport M σ)ᶜ = 0 := by
    apply orbitProbability_compl_range _ hs
    rw [orbitBasepoint_spec]
    exact Set.subset_iUnion (fun O : packetOrbits M σ => O.1) O
  simp only [Measure.smul_apply,H,smul_zero,tsum_zero]

end PrimeDegreePackets
end
end

end OAI
