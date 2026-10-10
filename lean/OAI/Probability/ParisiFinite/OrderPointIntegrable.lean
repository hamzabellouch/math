import Mathlib
import OAI.Probability.ParisiFinite.ScheduleWidthNonneg

namespace OAI

/-! Order Point Integrable. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

lemma orderPoint_integrable (ρ : ProbabilityMeasure OrderPoint) :
    Integrable (fun x : OrderPoint => (x:ℝ)) (ρ:Measure OrderPoint) := by
  apply (integrable_const (1:ℝ)).mono' continuous_subtype_val.aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg x.2.1] using x.2.2

lemma orderPoint_mean_zero_iff (ρ : ProbabilityMeasure OrderPoint) :
    (∫ x : OrderPoint,(x:ℝ) ∂(ρ:Measure OrderPoint))=0 ↔ ρ=zeroOrderMeasure := by
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all (ρ:Measure OrderPoint) fun x : OrderPoint => x.2.1)
      (orderPoint_integrable ρ)).mp h
    have he : (fun x : OrderPoint => x)=ᵐ[(ρ:Measure OrderPoint)]
        fun _ => (⟨0,by norm_num⟩ : OrderPoint) := hae.mono fun x hx => by
      apply Subtype.ext
      exact hx
    have hh : Measure.map (fun x : OrderPoint => x) (ρ:Measure OrderPoint)=
        Measure.map (fun _ : OrderPoint => (⟨0,by norm_num⟩ : OrderPoint)) (ρ:Measure OrderPoint) :=
      Measure.map_congr he
    change Measure.map id (ρ:Measure OrderPoint)=_ at hh
    rw [Measure.map_id] at hh
    apply Subtype.ext
    simp only [Measure.map_const,measure_univ,one_smul] at hh
    convert! hh using 1
  · rintro rfl
    simp [zeroOrderMeasure]

 

lemma minimizingParisi_mean_pos (β : ℝ≥0) (hb : (1:ℝ)<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    0<(∫ x : OrderPoint,(x:ℝ) ∂(ρ:Measure OrderPoint)) := by
  have hn : 0≤(∫ x : OrderPoint,(x:ℝ) ∂(ρ:Measure OrderPoint)) :=
    integral_nonneg fun x : OrderPoint => x.2.1
  apply lt_of_le_of_ne hn
  intro he
  have hzero := (orderPoint_mean_zero_iff ρ).mp he.symm
  subst ρ
  exact zeroOrderMeasure_not_minimizing β hb hρ

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma hasDerivAt_tiltedMean (f : SmoothField) {g g' : ℝ → ℝ}
    (hd : ∀ x,HasDerivAt g (g' x) x) (hc : Continuous g')
    {M N : ℝ≥0} (hM : ∀ x,|g x|≤M) (hN : ∀ x,|g' x|≤N) (a s x : ℝ) :
    HasDerivAt (tiltedMean a s f.val g)
      (tiltedMean a s f.val g' x+a*(tiltedMean a s f.val (fun y => f.d1 y*g y) x-
        tiltedMean a s f.val f.d1 x*tiltedMean a s f.val g x)) x := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have h := hasDerivAt_expMoment f.lipschitz f.hasD1 f.continuousD1 f.normD1
    hd hc hM hN a s x
  have he (y : ℝ) : a*f.d1 y*g y+g' y=g' y+a*(f.d1 y*g y) := by ring
  simp_rw [he] at h
  change HasDerivAt (expMoment a s f.val g)
    (expMoment a s f.val (fun y => g' y+a*(f.d1 y*g y)) x) x at h
  have hp : ∀ y,|a*(f.d1 y*g y)|≤|a| *((f.bound1:ℝ)*M) := by
    intro y
    rw [abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (f.normD1 y) (hM y) (abs_nonneg _) f.bound1.coe_nonneg) (abs_nonneg a)
  rw [expMoment_add (g := g') (h := fun y => a*(f.d1 y*g y)) f.lipschitz hc
    (by have hh := f.continuousD1;fun_prop) hN hp,expMoment_const_mul] at h
  have hh := h.div (hasDerivAt_expMass f a s x) (expMass_pos f.lipschitz a s x).ne'
  convert hh using 1 <;> first | rfl | (unfold tiltedMean;field_simp;ring)

structure ThirdJet (f : SmoothField) where
  d3 : ℝ → ℝ
  hasD3 : ∀ x,HasDerivAt f.d2 (d3 x) x
  continuousD3 : Continuous d3
  bound3 : ℝ≥0
  normD3 : ∀ x,|d3 x|≤bound3

namespace ThirdJet
variable {f : SmoothField}

def expThird (j : ThirdJet f) (a x : ℝ) : ℝ :=
  j.d3 x+3*a*(f.d1 x*f.d2 x)+a^2*(f.d1 x)^3

lemma continuous_expThird (j : ThirdJet f) (a : ℝ) : Continuous (j.expThird a) := by
  have h1 := f.continuousD1
  have h2 := f.continuousD2
  have h3 := j.continuousD3
  unfold expThird
  fun_prop

lemma product_bound (x : ℝ) : |f.d1 x*f.d2 x|≤ (f.bound1:ℝ)*f.bound2 := by
  rw [abs_mul]
  exact mul_le_mul (f.normD1 x) (f.normD2 x) (abs_nonneg _) f.bound1.coe_nonneg

lemma cube_bound (x : ℝ) : |f.d1 x^3|≤(f.bound1:ℝ)^3 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (f.normD1 x) 3

lemma expThird_bound (j : ThirdJet f) (a x : ℝ) :
    |j.expThird a x|≤j.bound3+3*|a| *((f.bound1:ℝ)*f.bound2)+a^2*(f.bound1:ℝ)^3 := by
  unfold expThird
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_add_le _ _) (le_refl _)).trans
  norm_num only [abs_mul,abs_of_nonneg (sq_nonneg a)]
  gcongr <;> first | exact j.normD3 x | exact f.normD1 x | exact f.normD2 x | exact cube_bound (f := f) x

 

def transformD3 (j : ThirdJet f) (a s x : ℝ) : ℝ :=
  tiltedMean a s f.val (j.expThird a) x-
    3*a*((f.transform a s).d1 x*(f.transform a s).d2 x)-
      a^2*((f.transform a s).d1 x)^3

lemma expThird_tilt (j : ThirdJet f) (a s x : ℝ) :
    tiltedMean a s f.val (j.expThird a) x=
      tiltedMean a s f.val j.d3 x+3*a*tiltedMean a s f.val (fun y => f.d1 y*f.d2 y) x+
        a^2*tiltedMean a s f.val (fun y => (f.d1 y)^3) x := by
  have h12 : Continuous (fun y => f.d1 y*f.d2 y) := f.continuousD1.mul f.continuousD2
  have h3 : Continuous (fun y => (f.d1 y)^3) := f.continuousD1.pow 3
  unfold expThird
  have hA : ∀ y,|3*a*(f.d1 y*f.d2 y)|≤|3*a| *((f.bound1:ℝ)*f.bound2) := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (product_bound y) (abs_nonneg _)
  have hB : ∀ y,|a^2*f.d1 y^3|≤|a^2| *(f.bound1:ℝ)^3 := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (cube_bound y) (abs_nonneg _)
  rw [tiltedMean_add (g := fun y => j.d3 y+3*a*(f.d1 y*f.d2 y))
    (h := fun y => a^2*f.d1 y^3) f.lipschitz
    (j.continuousD3.add (h12.const_mul _)) (h3.const_mul _)
    (fun y => (abs_add_le _ _).trans (add_le_add (j.normD3 y) (hA y))) hB,
    tiltedMean_add (g := j.d3) (h := fun y => 3*a*(f.d1 y*f.d2 y))
      f.lipschitz j.continuousD3 (h12.const_mul _) j.normD3 hA,
    tiltedMean_const_mul,tiltedMean_const_mul]

lemma hasDerivAt_transformD2 (j : ThirdJet f) (a s x : ℝ) :
    HasDerivAt (f.transform a s).d2 (j.transformD3 a s x) x := by
  have h2 := hasDerivAt_tiltedMean f j.hasD3 j.continuousD3 f.normD2 j.normD3 a s x
  have hc : Continuous (fun y => 2*(f.d1 y*f.d2 y)) :=
    (f.continuousD1.mul f.continuousD2).const_mul 2
  have hn : ∀ y,|2*(f.d1 y*f.d2 y)|≤(2*f.bound1*f.bound2:ℝ≥0) := by
    intro y
    have hh := mul_le_mul_of_nonneg_left (product_bound (f := f) y) (by norm_num : (0:ℝ)≤2)
    simpa only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),NNReal.coe_mul,NNReal.coe_ofNat,mul_assoc] using hh
  have hd : ∀ y,HasDerivAt (fun z => (f.d1 z)^2) (2*(f.d1 y*f.d2 y)) y := by
    intro y
    convert (f.hasD2 y).pow 2 using 1
    first | rfl | norm_num
    ring
  have hs := hasDerivAt_tiltedMean f hd hc (M := f.bound1^2)
    (by simpa only [NNReal.coe_pow] using sq_bound f.normD1) hn a s x
  have hh := h2.add ((hs.sub ((f.transform a s).hasD2 x |>.pow 2)).const_mul a)
  convert! hh using 1
  rw [transformD3,expThird_tilt]
  change _= _+ a*(_-2*(f.transform a s).d1 x ^ (2-1)*(f.transform a s).d2 x)
  have hcub : (fun y => f.d1 y*f.d1 y^2)=(fun y => f.d1 y^3) := by
    funext y;ring
  rw [hcub,tiltedMean_const_mul]
  simp only [SmoothField.transform]
  ring

lemma continuous_transformD3 (j : ThirdJet f) (a s : ℝ) : Continuous (j.transformD3 a s) := by
  have hb : ∀ y,|j.expThird a y|≤
      (j.bound3+3*Real.nnabs a*(f.bound1*f.bound2)+(Real.nnabs a)^2*f.bound1^3:ℝ≥0) := by
    intro y
    simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,Real.coe_nnabs,
      NNReal.coe_pow,sq_abs] using j.expThird_bound a y
  have hE := continuous_tiltedMean f.lipschitz (j.continuous_expThird a) hb a s
  have h1 := (f.transform a s).continuousD1
  have h2 := (f.transform a s).continuousD2
  unfold transformD3
  fun_prop

lemma transformD3_bound (j : ThirdJet f) (a s x : ℝ) :
    |j.transformD3 a s x|≤j.bound3+3*|a| *((f.bound1:ℝ)*f.bound2)+a^2*(f.bound1:ℝ)^3+
      3*|a| *((f.bound1:ℝ)*(f.transform a s).bound2)+a^2*(f.bound1:ℝ)^3 := by
  have ht := abs_tiltedMean_le f.lipschitz (j.continuous_expThird a) (j.expThird_bound a) a s x
  have h12 := product_bound (f := f.transform a s) x
  have h3 := cube_bound (f := f.transform a s) x
  unfold transformD3
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) (le_refl _)).trans
  norm_num only [abs_mul,abs_sq]
  calc
    _ ≤ (j.bound3+3*|a| *((f.bound1:ℝ)*f.bound2)+a^2*(f.bound1:ℝ)^3)+
        3*|a| *((f.bound1:ℝ)*(f.transform a s).bound2)+a^2*(f.bound1:ℝ)^3 := by
      gcongr <;> first | exact ht | exact (f.transform a s).normD1 x | exact (f.transform a s).normD2 x | exact h12 | exact h3
    _ = _ := rfl

def transform (j : ThirdJet f) (a s : ℝ) : ThirdJet (f.transform a s) where
  d3 := j.transformD3 a s
  hasD3 := j.hasDerivAt_transformD2 a s
  continuousD3 := j.continuous_transformD3 a s
  bound3 := j.bound3+3*Real.nnabs a*(f.bound1*f.bound2)+(Real.nnabs a)^2*f.bound1^3+
    3*Real.nnabs a*(f.bound1*(f.transform a s).bound2)+(Real.nnabs a)^2*f.bound1^3
  normD3 := fun x => by
    simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,Real.coe_nnabs,
      NNReal.coe_pow,sq_abs] using j.transformD3_bound a s x

lemma expThird_transform (j : ThirdJet f) (a s x : ℝ) :
    (j.transform a s).expThird a x=tiltedMean a s f.val (j.expThird a) x := by
  dsimp only [expThird,transform,transformD3]
  ring

end ThirdJet
end ParisiFinite

end

end OAI
