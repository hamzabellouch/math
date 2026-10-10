import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MicrocellHarmonic01
import OAI.Combinatorics.SumProduct.Alignment.PointLaw02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope1
open scoped Topology BigOperators
open Filter MeasureTheory Set
open scoped Topology BigOperators
open Filter MeasureTheory Set
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
open MeasureTheory Set Filter
namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
open MeasureTheory Set Filter

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

 

theorem beta_integrand_continuous (μ : ProbabilityMeasure X) (T : ℝ × X → Y)
    (hT : Measurable T) (hc : ∀ x, Continuous (fun β => T (β, x))) (F : Y →ᵇ E) :
    Continuous (fun β => ∫ x, F (T (β, x)) ∂(μ : Measure X)) := by
  apply continuous_of_dominated (bound := fun _ => ‖F‖)
  · intro β
    exact (F.continuous.measurable.comp
      (hT.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · intro β
    exact Eventually.of_forall (fun x => F.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Eventually.of_forall (fun x => F.continuous.comp (hc x))

 

def empiricalLaw (p : ℕ → Y) (N : ℕ) : ProbabilityMeasure Y :=
  if h : 0 < N then
    letI : NeZero N := ⟨h.ne'⟩
    uniformMixture (fun i : Fin N => (⟨Measure.dirac (p i.val), inferInstance⟩ : ProbabilityMeasure Y))
  else ⟨Measure.dirac (p 0), inferInstance⟩

lemma integral_empiricalLaw [CompleteSpace E] (p : ℕ → Y) (N : ℕ) (hN : 0 < N) (F : Y →ᵇ E) :
    ∫ y, F y ∂(empiricalLaw p N : Measure Y) =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, F (p n) := by
  let : NeZero N := ⟨hN.ne'⟩
  have he : empiricalLaw p N = uniformMixture
      (fun i : Fin N => (⟨Measure.dirac (p i.val), inferInstance⟩ : ProbabilityMeasure Y)) := by
    exact dite_eq_left hN
  rw [he]
  trans (Fintype.card (Fin N) : ℝ)⁻¹ • ∑ i : Fin N,
    ∫ y, F y ∂(Measure.dirac (p i.val))
  · exact integral_uniformMixture
      (fun i : Fin N => (⟨Measure.dirac (p i.val), inferInstance⟩ : ProbabilityMeasure Y)) F
  simp only [Fintype.card_fin, integral_dirac' F _ F.continuous.measurable.stronglyMeasurable,
    Finset.sum_range]

end
end SourcePointLaw

namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators BoundedContinuousFunction ENNReal NNReal
open MeasureTheory Set Filter

 

theorem empirical_tendsto_betaMixture
    {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (P : ℕ → ℤ → Y) (d : ℕ) [NeZero d]
    (X : Fin d → Type*) [∀ r, MeasurableSpace (X r)]
    (μ : ∀ r, ProbabilityMeasure (X r)) (T : ∀ r, ℝ × X r → Y)
    (hT : ∀ r, Measurable (T r))
    (hc : ∀ r x, Continuous (fun β => T r (β, x)))
    (hloc : ∀ r (F : Y →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L F →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > 0,
      ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      ∀ a b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 → b - a = α →
        ‖(𝔼 n ∈ residueInterval d r.val (a * N) (b * N), F (P N n)) -
            ∫ y, F (T r (x, y)) ∂(μ r : Measure (X r))‖ < ε) :
    Tendsto (fun N : ℕ => empiricalLaw (fun n => P N n) N) atTop
      (𝓝 (uniformMixture (fun r => betaImage (μ r) (T r) (hT r)))) := by
  apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb hl
  obtain ⟨L, hL⟩ := hl
  let F : Y →ᵇ ℝ := ⟨⟨f, hL.continuous⟩, hb⟩
  change Tendsto (fun N : ℕ => ∫ y, F y ∂(empiricalLaw (fun n => P N n) N : Measure Y))
    atTop (𝓝 (∫ y, F y ∂(uniformMixture (fun r => betaImage (μ r) (T r) (hT r)) : Measure Y)))
  rw [integral_uniformMixture]
  simp only [Fintype.card_fin, integral_betaImage]
  have hlim := global_point_law_fin (fun N n => F (P N n)) d (Nat.pos_of_ne_zero (NeZero.ne d))
    (fun r β => ∫ y, F (T r (β, y)) ∂(μ r : Measure (X r)))
    (fun r => (beta_integrand_continuous (μ r) (T r) (hT r) (hc r) F).continuousOn)
    (fun r => hloc r F L hL)
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  exact (integral_empiricalLaw (fun n => P N n) N (by omega) F).symm

end
end SourcePointLaw

end RawSuccessInlineScope1

 

 

section RawSuccessInlineScope2

 
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
namespace MicrocellProbability
variable {I Y : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Y]
open MicrocellHarmonic
attribute [local instance] Classical.propDecidable

lemma weight_pos (w:I→ℝ) (hw:∀ i,0<w i) (i:I) : 0<weight w i :=
  div_pos (hw i) (total_pos w hw)

 
def weightedLaw (w:I→ℝ) (hw:∀ i,0<w i) (p:I→Y) : ProbabilityMeasure Y :=
  ⟨∑ i,ENNReal.ofReal (weight w i) • Measure.dirac (p i), by
    constructor
    simp only [Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [←ENNReal.ofReal_sum_of_nonneg (fun i _=>(weight_pos w hw i).le),sum_weight w hw]
    norm_num⟩

 
def uniformLaw (p:I→Y) : ProbabilityMeasure Y :=
  SourcePointLaw.uniformMixture (fun i=>⟨Measure.dirac (p i),inferInstance⟩)

lemma weightedLaw_apply (w:I→ℝ) (hw:∀ i,0<w i) (p:I→Y)
    (S:Set Y) (hS:MeasurableSet S) :
    (weightedLaw w hw p:Measure Y).real S =
      ∑ i,weight w i*(if p i∈S then 1 else 0) := by
  classical
  change ( (∑ i,ENNReal.ofReal (weight w i) • Measure.dirac (p i):Measure Y) S).toReal=_
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hS]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi:p i∈S <;> simp [Set.indicator,hi,ENNReal.toReal_ofReal (weight_pos w hw i).le]
  · intro i _
    by_cases hi:p i∈S <;> simp [Set.indicator,hi]

lemma uniformLaw_apply (p:I→Y) (S:Set Y) (hS:MeasurableSet S) :
    (uniformLaw p:Measure Y).real S = ∑ i,uniform i*(if p i∈S then 1 else 0) := by
  classical
  change (((Fintype.card I : ℝ≥0∞)⁻¹ • (∑ i,Measure.dirac (p i)) : Measure Y) S).toReal = _
  simp only [Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,Measure.dirac_apply' _ hS]
  rw [ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:p i∈S <;> simp [uniform,Set.indicator,hi]
  · intro i _
    by_cases hi:p i∈S <;> simp [Set.indicator,hi]

 

theorem harmonic_event_error (x:I→ℝ) (X R:ℝ) (hX:0<X) (hR:0≤R)
    (hx:∀ i,X≤x i ∧ x i≤X+R) (p:I→Y) (S:Set Y) (hS:MeasurableSet S) :
    |(weightedLaw (fun i=>(x i)⁻¹) (fun i=>inv_pos.mpr (hX.trans_le (hx i).1)) p:Measure Y).real S -
      (uniformLaw p:Measure Y).real S| ≤ R/X := by
  rw [weightedLaw_apply _ _ _ _ hS,uniformLaw_apply _ _ hS]
  apply harmonic_test_error x X R hX hR hx
  intro i
  split_ifs <;> norm_num

 

theorem harmonic_success (x:I→ℝ) (X R c:ℝ) (hX:0<X) (hR:0≤R)
    (hx:∀ i,X≤x i ∧ x i≤X+R) (p:I→Y) (S:Set Y) (hS:MeasurableSet S)
    (hcell:R/X≤c/6) (hm:c/2<(uniformLaw p:Measure Y).real S) :
    c/3<(weightedLaw (fun i=>(x i)⁻¹) (fun i=>inv_pos.mpr (hX.trans_le (hx i).1)) p:Measure Y).real S := by
  have he:=harmonic_event_error x X R hX hR hx p S hS
  have he':= (abs_le.mp he).1
  linarith

lemma empiricalLaw_eq (p:ℕ→Y) (N:ℕ) (hN:0<N) :
    SourcePointLaw.empiricalLaw p N =
      @uniformLaw (Fin N) Y inferInstance (Fin.pos_iff_nonempty.mp hN) inferInstance (fun i=>p i) := by
  exact dite_eq_left hN

end MicrocellProbability
end
end RawSuccessInlineScope2

 

 

section RawSuccessInlineScope3
noncomputable section
open Filter Topology
namespace MicrocellScale

 
def radius (M H:ℕ) : ℕ := M*⌊Real.sqrt (H:ℝ)/(M:ℝ)⌋₊
def length (M H:ℕ) : ℕ := radius M H/M

lemma modulus_dvd (M H:ℕ) : M∣radius M H := dvd_mul_right _ _
lemma length_eq (M H:ℕ) (hM:0<M) : length M H=⌊Real.sqrt (H:ℝ)/(M:ℝ)⌋₊ :=
  Nat.mul_div_cancel_left _ hM

lemma radius_le (M H:ℕ) (hM:0<M) : (radius M H:ℝ) ≤ Real.sqrt (H:ℝ) := by
  have hm:(0:ℝ)<M:=by exact_mod_cast hM
  have hh:=Nat.floor_le (show 0≤Real.sqrt (H:ℝ)/(M:ℝ) by positivity)
  have hh':=mul_le_mul_of_nonneg_left hh hm.le
  simpa [radius,mul_div_cancel₀ _ hm.ne'] using hh'

lemma radius_gt (M H:ℕ) (hM:0<M) : Real.sqrt (H:ℝ)-(M:ℝ)<(radius M H:ℝ) := by
  have hm:(0:ℝ)<M:=by exact_mod_cast hM
  have hh:=Nat.lt_floor_add_one (Real.sqrt (H:ℝ)/(M:ℝ))
  have hh':=mul_lt_mul_of_pos_left hh hm
  have he:(M:ℝ)*(Real.sqrt (H:ℝ)/(M:ℝ))=Real.sqrt (H:ℝ):=mul_div_cancel₀ _ hm.ne'
  rw [he] at hh'
  simp only [radius,Nat.cast_mul]
  nlinarith

lemma radius_half_sqrt (M H:ℕ) (hM:0<M) (hH:4*(M:ℝ)^2≤H) :
    Real.sqrt (H:ℝ)/2 ≤ (radius M H:ℝ) := by
  have hs:(2:ℝ)*M≤Real.sqrt (H:ℝ):=(Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith)
  have hh:=radius_gt M H hM
  linarith

lemma sqrt_ratio (H S C:ℝ) (hH:0≤H) (hS:0<S) :
    Real.sqrt (H/S^(2*C))=Real.sqrt H/S^C := by
  rw [Real.sqrt_div hH]
  congr 1
  have he:S^(2*C)=(S^C)^2 := by rw [two_mul,Real.rpow_add hS]; ring
  rw [he,Real.sqrt_sq (Real.rpow_nonneg hS.le C)]

 
def Dominates (A S:ℕ→ℝ) : Prop :=
  ∀ C:ℝ,0<C → Tendsto (fun n=>A n/(S n)^C) atTop atTop

lemma sqrt_dominates {H:ℕ→ℕ} {S:ℕ→ℝ}
    (hS:∀ᶠ n in atTop,1≤S n) (hd: Dominates (fun n=>(H n:ℝ)) S)
    (C:ℝ) (hC:0<C) :
    Tendsto (fun n=>Real.sqrt (H n:ℝ)/(S n)^C) atTop atTop := by
  have hh:=Real.tendsto_sqrt_atTop.comp (hd (2*C) (by positivity))
  apply hh.congr'
  filter_upwards [hS] with n hn
  exact sqrt_ratio (H n) (S n) C (by positivity) (by linarith)

 

theorem radius_dominates {M H:ℕ→ℕ} {S:ℕ→ℝ}
    (hM:∀ᶠ n in atTop,0<M n ∧ (M n:ℝ)≤S n)
    (hS:∀ᶠ n in atTop,1≤S n) (hd:Dominates (fun n=>(H n:ℝ)) S) :
    Dominates (fun n=>(radius (M n) (H n):ℝ)) S := by
  intro C hC
  have hsmall:∀ᶠ n in atTop,4*(M n:ℝ)^2≤H n := by
    filter_upwards [hM,hS,(hd 2 (by norm_num)).eventually_ge_atTop 4] with n hm hs hh
    have hs0:0<S n:=by linarith
    rw [Real.rpow_two] at hh
    have hh':4*(S n)^2≤H n := (le_div_iff₀ (sq_pos_of_pos hs0)).mp hh
    have hm0:(0:ℝ)≤M n:=by positivity
    nlinarith
  have hc:=sqrt_dominates hS hd C hC
  have hh:Tendsto (fun n=>(Real.sqrt (H n:ℝ)/(S n)^C)/2) atTop atTop :=
    hc.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [hS,hM,hsmall] with n hs hm hn
  have hh:=radius_half_sqrt (M n) (H n) hm.1 hn
  have hp:0<(S n)^C:=Real.rpow_pos_of_pos (by linarith) C
  convert div_le_div_of_nonneg_right hh hp.le using 1
  ring

 

theorem boundary_rate {M H t:ℕ→ℕ} {S:ℕ→ℝ}
    (hM:∀ᶠ n in atTop,0<M n)
    (hS:∀ᶠ n in atTop,1≤S n)
    (ht:∀ᶠ n in atTop,(t n:ℝ)≤(S n)^2)
    (hd:Dominates (fun n=>(H n:ℝ)) S) :
    Tendsto (fun n=>(t n:ℝ)*radius (M n) (H n)/H n) atTop (𝓝 0) := by
  have hh:Tendsto (fun n=>(S n)^2/Real.sqrt (H n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div,Real.rpow_two] using
      tendsto_inv_atTop_zero.comp (sqrt_dominates hS hd 2 (by norm_num))
  have hp:∀ᶠ n in atTop,0<(H n:ℝ) := by
    filter_upwards [hS,(hd 1 (by norm_num)).eventually_ge_atTop 1] with n hs hn
    rw [Real.rpow_one] at hn
    have hpos:0<S n:=by linarith
    have hpn:1*S n≤H n:=(le_div_iff₀ hpos).mp hn
    linarith
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n=>by positivity)) ?_ hh
  filter_upwards [hM,ht,hp] with n hm ht hn
  have hs:0<Real.sqrt (H n:ℝ):=Real.sqrt_pos_of_pos hn
  calc
    _ ≤ (S n)^2*Real.sqrt (H n:ℝ)/H n := by
      apply div_le_div_of_nonneg_right _ hn.le
      exact mul_le_mul ht (radius_le _ _ hm) (by positivity) (sq_nonneg _)
    _ = _ := by
      have he:=Real.sq_sqrt hn.le
      field_simp
      nlinarith

 
theorem endpoint_rate {M H X:ℕ→ℕ}
    (hM:∀ᶠ n in atTop,0<M n)
    (hH:∀ᶠ n in atTop,0<H n)
    (hd:Tendsto (fun n=>Real.log (X n:ℝ)/(H n:ℝ)) atTop atTop) :
    Tendsto (fun n=>(radius (M n) (H n):ℝ)/X n) atTop (𝓝 0) := by
  have hh:Tendsto (fun n=>(X n:ℝ)/(H n:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hd
    exact Filter.Eventually.of_forall (fun n=>div_le_div_of_nonneg_right
      (Real.log_le_self (by positivity)) (by positivity))
  have hz:Tendsto (fun n=>(H n:ℝ)/(X n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_atTop_zero.comp hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n=>by positivity)) ?_ hz
  filter_upwards [hM,hH] with n hm hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (radius_le _ _ hm).trans
  apply Real.sqrt_le_iff.mpr
  have hn':(1:ℝ)≤H n:=by exact_mod_cast hn
  constructor <;> nlinarith

end MicrocellScale

end
end RawSuccessInlineScope3
end

end OAI
