import Mathlib
import OAI.NumberTheory.PrimePackets.ErgodicDecomposition

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
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
namespace PrimeDegreePackets
open MeasureTheory Filter Set

lemma rightAction_transitive (n : ℕ) (x y : X n) : ∃ g : G n, rightAction x g = y := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  obtain ⟨b,rfl⟩ := Quotient.exists_rep y
  refine ⟨a⁻¹*b,?_⟩
  change Quotient.mk _ (a*(a⁻¹*b)) = Quotient.mk _ b
  simp

 

theorem isHaarProbability_unique {n : ℕ} {μ ν : Measure (X n)}
    (hμ : IsHaarProbability μ) (hν : IsHaarProbability ν) : μ = ν := by
  let : MeasurableSpace (G n) := borel (G n)
  let : BorelSpace (G n) := ⟨rfl⟩
  have : IsProbabilityMeasure μ := hμ.1
  have : IsProbabilityMeasure ν := hν.1
  exact invariant_probability_unique_transitive (@rightAction n)
    (continuous_rightAction_uncurry n).measurable
    (fun g => (rightActionHomeomorph g).toMeasurableEquiv) (fun _ _ => rfl)
    (fun x g h => rightAction_mul x g h) (rightAction_transitive n)
    (Measure.haar : Measure (G n)) μ ν hμ.2 hν.2

end PrimeDegreePackets


namespace PrimeDegreePackets
open Filter Set Topology

lemma idealCoefficient_abscissa_le_one (K : Type*) [Field K] [NumberField K] :
    LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact idealCoefficient_LSeriesSummable K (by simpa using hy)

lemma dedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
  have hab : LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) < s.re :=
    (idealCoefficient_abscissa_le_one K).trans_lt (by exact_mod_cast hs)
  have H := (LSeries_hasDerivAt hab).differentiableAt
  have heq : LSeries (fun m => (idealCoefficientReal K m : ℂ)) =
      NumberField.dedekindZeta K := funext (idealCoefficient_LSeries_eq K)
  rw [heq] at H
  exact H

 

def regularizedDedekindZeta (K : Type*) [Field K] [NumberField K] (h : ℝ) : ℝ :=
  h*(NumberField.dedekindZeta K (1+h)).re

def logRegularizedDedekindZeta (K : Type*) [Field K] [NumberField K] (h : ℝ) : ℝ :=
  Real.log (regularizedDedekindZeta K h)

lemma regularizedDedekindZeta_pos (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : 0 < regularizedDedekindZeta K h := by
  have H := dedekindZeta_real_one_le K (s := 1+h) (by linarith)
  have H' : 1 ≤ (NumberField.dedekindZeta K (1+h)).re := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using H
  exact mul_pos hh (lt_of_lt_of_le zero_lt_one H')

lemma regularizedDedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : DifferentiableAt ℝ (regularizedDedekindZeta K) h := by
  have H := (dedekindZeta_differentiableAt K (s := (1+h:ℝ)) (by simpa using (show 1 < 1+h by linarith))).hasDerivAt.real_of_complex
  have H' := H.comp h ((hasDerivAt_id h).const_add 1)
  have H'' := (hasDerivAt_id h).mul H'
  change DifferentiableAt ℝ (fun h : ℝ => h*(NumberField.dedekindZeta K (1+(h:ℂ))).re) h
  simpa only [Function.comp_def, Pi.mul_def, id_eq, Complex.ofReal_add,Complex.ofReal_one]
    using H''.differentiableAt

lemma logRegularizedDedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : DifferentiableAt ℝ (logRegularizedDedekindZeta K) h :=
  (regularizedDedekindZeta_differentiableAt K hh).log (regularizedDedekindZeta_pos K hh).ne'

lemma tendsto_regularizedDedekindZeta (K : Type*) [Field K] [NumberField K] :
    Tendsto (regularizedDedekindZeta K) (𝓝[>] 0) (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have H := tendsto_residue_from_right K
  change Tendsto (fun h : ℝ => h*(NumberField.dedekindZeta K (1+(h:ℂ))).re) _ _
  simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_one] using H

lemma tendsto_logRegularizedDedekindZeta (K : Type*) [Field K] [NumberField K] :
    Tendsto (logRegularizedDedekindZeta K) (𝓝[>] 0)
      (𝓝 (Real.log (NumberField.dedekindZeta_residue K))) :=
  (tendsto_regularizedDedekindZeta K).log (NumberField.dedekindZeta_residue_ne_zero K)

 

theorem residue_log_comparison_of_deriv_bound (K : Type*) [Field K] [NumberField K]
    {B C : ℝ} (hB : 0 < B)
    (H : ∀ h ∈ Ioc (0:ℝ) B, |deriv (logRegularizedDedekindZeta K) h| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    |logRegularizedDedekindZeta K h - Real.log (NumberField.dedekindZeta_residue K)| ≤ C*h := by
  have H' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      |logRegularizedDedekindZeta K h-logRegularizedDedekindZeta K u| ≤ C*|h-u| := by
    filter_upwards [self_mem_nhdsWithin,
      (show Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) from tendsto_id.mono_left inf_le_left).eventually_lt_const hB]
      with u hu huB
    have HM := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u (hu : u ∈ Ioc (0:ℝ) B) => logRegularizedDedekindZeta_differentiableAt K hu.1)
      (fun u hu => by simpa only [Real.norm_eq_abs] using H u hu)
      (convex_Ioc (0:ℝ) B) ⟨hu,huB.le⟩ ⟨hh,hhB⟩
    simpa only [Real.norm_eq_abs] using HM
  have Hleft := ((tendsto_const_nhds (x := logRegularizedDedekindZeta K h)).sub
    (tendsto_logRegularizedDedekindZeta K)).abs
  have Hright : Tendsto (fun u : ℝ => C*|h-u|) (𝓝[>] 0) (𝓝 (C*h)) := by
    have Habs := ((tendsto_const_nhds (x := h)).sub
      (tendsto_id.mono_left inf_le_left : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0))).abs
    simpa only [sub_zero,abs_of_pos hh,id_eq] using Habs.const_mul C
  exact le_of_tendsto_of_tendsto Hleft Hright H'

 
theorem residue_comparison_of_deriv_bound (K : Type*) [Field K] [NumberField K]
    {B C : ℝ} (hB : 0 < B)
    (H : ∀ h ∈ Ioc (0:ℝ) B, |deriv (logRegularizedDedekindZeta K) h| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    Real.exp (-C*h)*NumberField.dedekindZeta_residue K ≤ regularizedDedekindZeta K h ∧
      regularizedDedekindZeta K h ≤ Real.exp (C*h)*NumberField.dedekindZeta_residue K := by
  have HL := residue_log_comparison_of_deriv_bound K hB H hh hhB
  have Htwo := abs_le.mp HL
  have hreg := regularizedDedekindZeta_pos K hh
  have hk := NumberField.dedekindZeta_residue_pos K
  constructor
  · have E := Real.exp_le_exp.mpr (show -C*h+Real.log (NumberField.dedekindZeta_residue K) ≤
        Real.log (regularizedDedekindZeta K h) by
      have hhlo := Htwo.1
      change -(C*h) ≤ Real.log (regularizedDedekindZeta K h)-_ at hhlo
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg] using E
  · have E := Real.exp_le_exp.mpr (show Real.log (regularizedDedekindZeta K h) ≤
        C*h+Real.log (NumberField.dedekindZeta_residue K) by
      have hhhi := Htwo.2
      change Real.log (regularizedDedekindZeta K h)-_ ≤ C*h at hhhi
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg] using E

end PrimeDegreePackets


namespace PrimeDegreePackets

 

def realPoleKernel (X Y U : ℝ) : ℝ := (X+U) / ((X+U)^2+Y^2)

lemma realPoleKernel_nonneg {X Y U : ℝ} (hX : 0 ≤ X) (hU : 0 ≤ U) :
    0 ≤ realPoleKernel X Y U := by
  exact div_nonneg (add_nonneg hX hU) (add_nonneg (sq_nonneg _) (sq_nonneg _))

 

theorem realPoleKernel_comparison {c X Y U : ℝ} (hc : 0 < c)
    (hX : 0 ≤ X) (hU : 0 < U) (hU4 : U ≤ 4) (hgap : c^2 ≤ X^2+Y^2) :
    realPoleKernel X Y U ≤ 4*(1+3/c)^2 * realPoleKernel X Y 1 := by
  let q := (X+U)^2+Y^2
  let q₀ := (X+1)^2+Y^2
  have hcq : c^2 ≤ q := by dsimp [q]; nlinarith
  have hq : 0 < q := lt_of_lt_of_le (sq_pos_of_pos hc) hcq
  have hq₀ : 0 < q₀ := by dsimp [q₀]; nlinarith [sq_nonneg Y]
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hcs : c ≤ Real.sqrt q := by nlinarith
  have hAs : X+U ≤ Real.sqrt q := by
    have hqY : (X+U)^2 ≤ q := by dsimp [q]; nlinarith [sq_nonneg Y]
    nlinarith
  have hdiff : (1-U)^2 ≤ 9 := by nlinarith
  have hterm : 2*(X+U)*(1-U) ≤ 6*Real.sqrt q := by
    have h1 : 2*(X+U)*(1-U) ≤ 6*(X+U) := by nlinarith
    linarith
  have hq₀s : q₀ ≤ (Real.sqrt q+3)^2 := by
    have he : q₀ = q + 2*(X+U)*(1-U) + (1-U)^2 := by dsimp [q₀,q]; ring
    rw [he]
    nlinarith
  have hfactor : 0 < 1+3/c := by positivity
  have hscale : Real.sqrt q+3 ≤ (1+3/c)*Real.sqrt q := by
    have H := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 3/c by positivity)
    have he : (3/c)*c = 3 := by field_simp
    rw [he] at H
    nlinarith
  have hratio : q₀ ≤ (1+3/c)^2*q := by
    calc
      q₀ ≤ (Real.sqrt q+3)^2 := hq₀s
      _ ≤ ((1+3/c)*Real.sqrt q)^2 := pow_le_pow_left₀ (by positivity) hscale 2
      _ = (1+3/c)^2*q := by rw [mul_pow,hsq]
  have hx : X+U ≤ 4*(X+1) := by linarith
  have hmul := mul_le_mul hx hratio hq₀.le (by linarith : 0 ≤ 4*(X+1))
  unfold realPoleKernel
  change (X+U)/q ≤ 4*(1+3/c)^2*((X+1)/q₀)
  rw [← mul_div_assoc,le_div_iff₀ hq₀,div_mul_eq_mul_div,div_le_iff₀ hq]
  nlinarith only [hmul]

 

theorem tsum_realPoleKernel_comparison {ι : Type*} {c U : ℝ}
    (X Y : ι → ℝ) (hc : 0 < c) (hX : ∀ i, 0 ≤ X i)
    (hU : 0 < U) (hU4 : U ≤ 4) (hgap : ∀ i, c^2 ≤ (X i)^2+(Y i)^2)
    (hs : Summable (fun i => realPoleKernel (X i) (Y i) 1)) :
    Summable (fun i => realPoleKernel (X i) (Y i) U) ∧
    0 ≤ ∑' i, realPoleKernel (X i) (Y i) U ∧
    (∑' i, realPoleKernel (X i) (Y i) U) ≤
      4*(1+3/c)^2 * (∑' i, realPoleKernel (X i) (Y i) 1) := by
  have hb (i : ι) := realPoleKernel_comparison hc (hX i) hU hU4 (hgap i)
  have hn (i : ι) := realPoleKernel_nonneg (Y := Y i) (hX i) hU.le
  have hsum := (hs.mul_left (4*(1+3/c)^2)).of_nonneg_of_le hn hb
  refine ⟨hsum,tsum_nonneg hn,?_⟩
  simpa only [tsum_mul_left] using hsum.tsum_le_tsum hb (hs.mul_left (4*(1+3/c)^2))

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem fieldDiscriminant_le_packetScale_sq {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) :
    |(NumberField.discr K : ℝ)| ≤ (packetScale M)^2 := by
  have hq : (1:ℝ) ≤ saturationIndex M := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (saturationIndex_ne_zero M)
  have hD := abs_nonneg (NumberField.discr K : ℝ)
  have hs : Real.sqrt |(NumberField.discr K : ℝ)| ≤ packetScale M := by
    unfold packetScale
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hq
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  simpa only [Real.sq_sqrt hD] using H

 

theorem weightedIdeal_realInterval_of_zeta_scale (n : ℕ) (hn0 : 0 < n)
    {A : ℝ} (hA : 0 < A)
    (Hscale : ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
        (K →+* ℝ) → Module.finrank ℚ K = n →
        |(NumberField.discr K : ℝ)| ≤ Q^2 →
        ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            A*NumberField.dedekindZeta_residue K) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice n K), (K →+* ℝ) →
        Module.finrank ℚ K = n → |(NumberField.discr K : ℝ)| ≤ Q^2 →
        (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q → η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_realInterval_zeta_bound n hn0
  refine ⟨C*A,mul_pos hC hA,?_⟩
  intro A₀ hA₀ η hη
  filter_upwards [H A₀ hA₀ η hη,Hscale,eventually_ge_atTop (0:ℝ)] with Q hQ hscale hQ0
  intro K _ _ _ M σ hn hD hq x y hxl hxu hrel hyx
  have hceil : Q^(3/4:ℝ) ≤ (⌈x⌉₊:ℝ) := hxl.trans (Nat.le_ceil x)
  have HR := hscale K σ hn hD _ hceil
  have hy : 0 ≤ y := le_trans (mul_nonneg hη.le (le_trans (Real.rpow_nonneg hQ0 _) hxl)) hrel
  apply (hQ K M hn hq x y hxl hxu hrel hyx).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*y*((NumberField.dedekindZeta K (1+1/Real.log (⌈x⌉₊:ℝ))).re /
        Real.log (⌈x⌉₊:ℝ)) ≤ C*y*(A*NumberField.dedekindZeta_residue K) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hy)
      simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_one,
        Complex.ofReal_div] using HR
    _ = _ := by ring

 

def UniformZetaScaleBound (n : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ Q : ℝ in atTop,
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      (K →+* ℝ) → Module.finrank ℚ K = n →
      |(NumberField.discr K : ℝ)| ≤ Q^2 →
      ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
          A*NumberField.dedekindZeta_residue K

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators

 
theorem packet_box_moment_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ B r₀ : ℝ, 0 < B ∧ 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ w : Fin (d+1) → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*ε^(d+1)) := by
  obtain ⟨R,hR,HR⟩ := Hscale
  obtain ⟨A,hA,Hcount⟩ := weightedIdeal_realInterval_of_zeta_scale (d+1) (by omega) hR HR
  obtain ⟨r₀,hr₀,Hpar⟩ := box_interval_parameters (n := d+1) (by omega) hb hc
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let A₀ : ℝ := b^(d+1)+2*C+1
  let B : ℝ := (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*(A*4*C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,r₀,hB,hr₀,?_⟩
  intro ε hε hεr
  obtain ⟨hεc,hε1,hA₀,hη,Hε⟩ := Hpar ε hε hεr
  filter_upwards [Hε,Hcount A₀ hA₀ (4*C*ε/A₀) hη] with Q hQ hcount
  intro K _ _ _ M σ hn hscale w hwlo hwhi
  obtain ⟨hxl,hxu,hrel,hyx⟩ := hQ.2 w hwlo hwhi
  have hq : (saturationIndex M:ℝ) ≤ Q := hscale ▸ saturationIndex_le_packetScale M
  have H := hcount K M (σ 0) hn (hscale ▸ fieldDiscriminant_le_packetScale_sq M) hq _ _ hxl hxu hrel hyx
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

 
theorem packet_cube_moment_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
          (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*(θ^(d+1)+(Real.log Q)^d/Q^(1/4:ℝ))) := by
  obtain ⟨R,hR,HR⟩ := Hscale
  obtain ⟨C,hC,Hcount⟩ := weightedIdeal_realInterval_of_zeta_scale (d+1) (by omega) hR HR
  let s : ℝ := Fintype.card (Fin (d+1) → SignTypeˣ)
  let B := s*C*(logMomentConstant d+1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hL := logMomentConstant_nonneg d
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hcount 1 le_rfl 1 zero_lt_one,eventually_ge_atTop (1:ℝ)] with Q hcount hQ
  intro K _ _ _ M σ hn hMQ θ hθ hθ1
  have hQ' : 1 ≤ packetScale M := hMQ ▸ hQ
  have H := packetMeasure_cube_moment_of_count M σ hn hodd hθ hθ1 hC.le hQ' (by
    intro t ht htQ
    apply hcount K M (σ 0) hn (hMQ ▸ fieldDiscriminant_le_packetScale_sq M) (by rw [← hMQ]; exact saturationIndex_le_packetScale M) t t
    · simpa only [hMQ] using ht
    · simpa only [one_mul,hMQ] using htQ
    · simp
    · rfl)
  apply H.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hMQ]
  have he : 0 ≤ (Real.log Q)^d/Q^(1/4:ℝ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg hQ) _) (Real.rpow_nonneg (by linarith) _)
  have hθn := pow_nonneg hθ.le (d+1)
  dsimp only [B,s]
  nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) (mul_nonneg hL he)]

 
theorem packet_ball_bound_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ x ∈ Ω, packetMeasure M σ ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
          ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨b,c,hb,hc,Hvec⟩ := compact_uniform_vector_envelope hΩ
  obtain ⟨A,ε₀,hA,hε₀,Hbox⟩ := packet_box_moment_of_zeta_scale d hodd Hscale hb.le hc
  let E : ℝ := (d+1:ℕ)*b
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨A*E^(d+1),ε₀/E,by positivity,div_pos hε₀ hE,?_⟩
  intro r hr hrr
  have hrε : E*r < ε₀ := by nlinarith [(lt_div_iff₀ hE).mp hrr]
  filter_upwards [Hbox (E*r) (mul_pos hE hr) hrε] with Q hQ
  intro K _ _ _ M σ hn hMQ x hx
  obtain ⟨g,hg,z,hz⟩ := Hvec x hx
  have hzne : z ≠ 0 := by
    intro he
    have H : c < (0:ℝ) := by simpa [he,Matrix.vecMul,dotProduct] using (hz 0).1
    exact hc.not_gt H
  have hlo (i) : c ≤ |integerRowMap g.1 z i| := by
    simpa only [integerRowMap_apply] using (hz i).1.le
  have hhi (i) : |integerRowMap g.1 z i| ≤ b := by
    simpa only [integerRowMap_apply] using (hz i).2.le
  have hsum : (∑ i, |integerRowMap g.1 z i|) ≤ E := by
    calc
      _ ≤ ∑ _ : Fin (d+1), b := Finset.sum_le_sum fun i _ => hhi i
      _ = E := by simp [E]
  have H := right_ball_mass_le_box_moment (packetMeasure M σ) g z hzne hr.le
    (show r*(∑ i, |integerRowMap g.1 z i|) ≤ E*r by nlinarith)
  rw [hg] at H
  refine H.trans ((hQ K M σ hn hMQ (integerRowMap g.1 z) hlo hhi).trans_eq ?_)
  congr 1
  rw [mul_pow]
  ring

 
theorem packet_limit_ball_bound_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      (ν : Measure (X (d+1))) ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
        ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨C,r₀,hC,hr₀,H⟩ := packet_ball_bound_of_zeta_scale d hodd Hscale hΩ
  refine ⟨C,r₀,hC,hr₀,?_⟩
  intro x hx r hr hrr
  apply open_mass_le_of_probability_limit _ ν hlim (right_ball_isOpen x r)
  filter_upwards [hQ.eventually (H r hr hrr)] with i hi
  exact hi (K i) (M i) (σ i) (hn i) rfl x hx

 
theorem packet_tight_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop) :
    IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  obtain ⟨B,hB,Hcube⟩ := packet_cube_moment_of_zeta_scale d hodd Hscale
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [hεtop]⟩
  let e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  let θ := min (1/2:ℝ) (e/(4*B))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos he (by positivity))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθe : B*θ^(d+1) ≤ e/4 := by
    have hpow : θ^(d+1) ≤ θ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hθ.le (pow_le_one₀ hθ.le hθ1)
    have he' := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_right (1/2:ℝ) (e/(4*B)))
    dsimp only [θ] at hpow ⊢
    nlinarith
  have Herror := ((cusp_log_error_vanishes d).comp hQ).eventually_lt_const
    (show (0:ℝ) < e/(4*B) by positivity)
  have Hmass : ∀ᶠ i in atTop,
      packetMeasure (M i) (σ i) (thickLattices (d+1) θ)ᶜ ≤ ε := by
    filter_upwards [hQ.eventually Hcube,Herror] with i hi herror
    apply (cusp_mass_le_cube_moment (packetMeasure (M i) (σ i)) θ).trans
    apply (hi (K i) (M i) (σ i) (hn i) rfl θ hθ hθ1).trans
    rw [← ENNReal.ofReal_toReal hεtop]
    apply ENNReal.ofReal_le_ofReal
    have H := (lt_div_iff₀ (show 0 < 4*B by positivity)).mp herror
    dsimp only [Function.comp_apply] at H
    change B*(θ^(d+1)+(Real.log (packetScale (M i)))^d/(packetScale (M i))^(1/4:ℝ)) ≤ e
    nlinarith
  obtain ⟨i₀,Hi⟩ := eventually_atTop.mp Hmass
  let F : Set (X (d+1)) := ⋃ i : Fin i₀, packetSupport (M i) (σ i)
  have hF : IsCompact F := isCompact_iUnion fun i : Fin i₀ =>
    packetSupport_isCompact (M i) (σ i) (hn i) hodd
  refine ⟨thickLattices (d+1) θ ∪ F,(mahler_compact d θ hθ).union hF,?_⟩
  rintro μ ⟨i,rfl⟩
  by_cases hi : i₀ ≤ i
  · exact (measure_mono (Set.compl_subset_compl.mpr Set.subset_union_left)).trans (Hi i hi)
  · have hs : packetSupport (M i) (σ i) ⊆ thickLattices (d+1) θ ∪ F := by
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,Nat.lt_of_not_ge hi⟩,hx⟩)
    apply (measure_mono (Set.compl_subset_compl.mpr hs)).trans
    rw [packetMeasure_compl_support (M i) (σ i) (hn i) hodd]
    exact bot_le

 
theorem packet_probability_subsequence_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    ∃ (ν : ProbabilityMeasure (X (d+1))) («φ» : ℕ → ℕ), StrictMono «φ» ∧
      Tendsto (fun i => packetProbability (M («φ» i)) (σ («φ» i)) (hn («φ» i)) hodd)
        atTop (𝓝 ν) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_of_zeta_scale d hodd Hscale K M σ hn hQ
  let p := fun i => packetProbability (M i) (σ i) (hn i) hodd
  have ht : IsTightMeasureSet {((μ : ProbabilityMeasure (X (d+1))) : Measure (X (d+1))) |
      μ ∈ Set.range p} := by
    convert htight using 1
    ext μ
    simp only [Set.mem_ofPred_eq,Set.mem_range]
    constructor
    · rintro ⟨ν,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨p i,⟨i,rfl⟩,rfl⟩
  obtain ⟨ν,_,«φ»,hφ,hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
      (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν,«φ»,hφ,hlim⟩

 

theorem packet_limit_positive_ergodic_components_of_zeta_scale
    (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν)) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel (ν : Measure (X (d+1))) m ∘ₘ (ν : Measure (X (d+1))).trim hm = ν ∧
      ∀ᵐ z ∂(ν : Measure (X (d+1))).trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
          (condExpKernel (ν : Measure (X (d+1))) m z) ∧
        0 < measureEntropy (condExpKernel (ν : Measure (X (d+1))) m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  apply diagonal_positive_ergodic_decomposition d ν
  · exact packet_limit_diagonal_invariant d hodd K M σ hn ν hlim
  · intro Ω hΩ
    exact packet_limit_ball_bound_of_zeta_scale d hodd Hscale K M σ hn hQ ν hlim hΩ

end PrimeDegreePackets
end
end

end OAI
