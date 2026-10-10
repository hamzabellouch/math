import Mathlib
import OAI.Geometry.BallPacking.Toric.RestrictedMassIndependence

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold ContinuousLinearMap
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem coefficientNorm_chart_hasFDerivAt (D m : ℕ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    HasFDerivAt (fun z => coefficientNorm D m ((extChartAt 𝓘(ℝ,RealModel) b).symm z))
      ((2:ℝ) • (phaseDot (weightedPhaseInclusion D m ((extChartAt 𝓘(ℝ,RealModel) b).symm y))).comp
        (realPhaseDerivative (fderiv ℂ (weightedChart D m b) (Complex.equivRealProdCLM.symm y)))) y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)
  have hd := ((weightedPhaseInclusion_smooth D m).contMDiffAt.comp y hi).contDiffAt.differentiableAt (by simp)
  have hf := (weighted_phase_chart_derivative D m b hy)
  rw [manifoldMapDifferential,mfderiv_eq_fderiv] at hf
  have h := ((phaseSq_hasFDerivAt _).comp y hd.hasFDerivAt).const_add 1
  rw [hf] at h
  exact h

 theorem weightedFSPrimitive_chart_log (D m : ℕ) (c : ℝ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    chartOneForm (weightedFSPrimitive D m c) b y (0,1)=
      c/4*(fderiv ℝ (fun z => Real.log (coefficientNorm D m
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z))) y (1,0)) ∧
    chartOneForm (weightedFSPrimitive D m c) b y (1,0)=
      -(c/4)*(fderiv ℝ (fun z => Real.log (coefficientNorm D m
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z))) y (0,1)) := by
  have hl := (coefficientNorm_chart_hasFDerivAt D m b hy).log
    (coefficientNorm_pos D m ((extChartAt 𝓘(ℝ,RealModel) b).symm y)).ne'
  rw [hl.fderiv]
  rw [weightedFSPrimitive,chartOneForm_manifoldPullback (weightedPhaseInclusion_smooth D m) (p := (0,y)) hy]
  change affineFSPrimitive c _
      (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
        (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))=_ ∧
    affineFSPrimitive c _
      (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
        (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))=_
  rw [weighted_phase_chart_derivative D m b hy,realPhaseDerivative_I]
  simp only [affineFSPrimitive,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,Function.comp_apply,
    realPhaseDerivative_I,phaseDot_J_right,phaseArea_J_right,coefficientNorm]
  constructor <;> field_simp [(fs_den_pos _).ne'] <;> ring

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
open ContinuousLinearMap
open Hamiltonian

variable {ι E F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 omit [Nonempty ι] [FiniteDimensional ℝ E] in
 theorem constrained_log_derivative {w : ι → E} {q d h : ι → ℝ} (_hq : ∀ i,0<q i)
    (hs : ∑ i,d i=0) (hm : ∑ i,d i • w i=0) {z : E} {C : ℝ}
    (he : ∀ i,d i/q i=h i+inner ℝ (w i) z-C) :
    (∑ i,d i*h i)=∑ i,(d i)^2/q i := by
  have hi : ∑ i,d i*inner ℝ (w i) z=0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using congrArg (fun v => inner ℝ v z) hm
  have hh (i : ι) : d i*h i=(d i)^2/q i-d i*inner ℝ (w i) z+d i*C := by
    have hh : h i=d i/q i-inner ℝ (w i) z+C := by linarith [he i]
    rw [hh]
    ring
  simp_rw [hh]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hi,←Finset.sum_mul,hs,zero_mul,sub_zero,add_zero]

 theorem selected_coeff_differentiableAt {w : ι → E} {a : F → ι → ℝ} {x : F}
    (ha : ∀ i,0<a x i) {p : E} (hp : Surrounds w p) (hA : DifferentiableAt ℝ a x) (i : ι) :
    DifferentiableAt ℝ (fun y => selected w (a y) p i) x := by
  have hs : DifferentiableAt ℝ (fun z : (ι → ℝ) × E => selected w z.1 z.2 i) (a x,p) :=
    (selected_contDiffAt ha hp i).differentiableAt (by simp)
  exact hs.comp x (hA.prodMk (differentiableAt_const p))

 theorem selected_log_variation {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) (v : F) :
    (∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
      (fderiv ℝ (fun y => Real.log (a y i)) x v))=
      ∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)^2/selected w (a x) p i := by
  let q : F → ι → ℝ := fun y i => selected w (a y) p i
  let X : F → E := fun y => inverse w (a y) p
  let P : F → ℝ := fun y => partition w (a y) (X y)
  have hq (i : ι) : DifferentiableAt ℝ (fun y => q y i) x :=
    selected_coeff_differentiableAt (ha x) hp hA i
  have hX : DifferentiableAt ℝ X x := by
    have hi : DifferentiableAt ℝ (fun z : (ι → ℝ) × E => inverse w z.1 z.2) (a x,p) :=
      (inverse_contDiffAt (ha x) hp).differentiableAt (by simp)
    exact hi.comp x (hA.prodMk (differentiableAt_const p))
  have ha' (i : ι) : DifferentiableAt ℝ (fun y => a y i) x :=
    (differentiableAt_pi.mp hA) i
  have hP : DifferentiableAt ℝ P x := DifferentiableAt.fun_sum
    (fun i _ => (ha' i).mul (((differentiableAt_const (w i)).inner ℝ hX).exp))
  have hs : ∑ i,fderiv ℝ (fun y => q y i) x v=0 := by
    have he : (fun y => ∑ i,q y i)=(fun _ : F => (1:ℝ)) := funext (fun y => selected_sum (ha y) p)
    have hd := congrArg (fun f : F → ℝ => fderiv ℝ f x v) he
    simpa only [fderiv_fun_sum (fun i _ => hq i),sum_apply,fderiv_fun_const,Pi.zero_apply,zero_apply] using hd
  have hm : ∑ i,(fderiv ℝ (fun y => q y i) x v) • w i=0 := by
    have he : (fun y => ∑ i,q y i • w i)=(fun _ : F => p) := funext (fun y => selected_mean (ha y) hp)
    have hd := congrArg (fun f : F → E => fderiv ℝ f x v) he
    have hsmi (i : ι) := (hq i).smul_const (w i)
    simpa only [fderiv_fun_sum (fun i _ => hsmi i),fderiv_smul_const (hq _),sum_apply,
      ContinuousLinearMap.smulRight_apply,fderiv_fun_const,Pi.zero_apply,zero_apply] using hd
  apply constrained_log_derivative (fun i => selected_pos (ha x) p i) hs hm
    (z := fderiv ℝ X x v) (C := fderiv ℝ (fun y => Real.log (P y)) x v)
  intro i
  have he : (fun y => Real.log (q y i))=(fun y => Real.log (a y i)+inner ℝ (w i) (X y)-Real.log (P y)) :=
    funext (fun y => gibbs_log (ha y) (X y) i)
  have hd := congrArg (fun f : F → ℝ => fderiv ℝ f x v) he
  have hql := (hq i).hasFDerivAt.log (selected_pos (ha x) p i).ne'
  have hal := (ha' i).log (ha x i).ne'
  have hpl := hP.log (partition_pos (ha x) (X x)).ne'
  have hinner := (innerSL ℝ (w i)).hasFDerivAt.comp x hX.hasFDerivAt
  change HasFDerivAt (fun y => inner ℝ (w i) (X y))
    ((innerSL ℝ (w i)).comp (fderiv ℝ X x)) x at hinner
  have hright := (hal.hasFDerivAt.add hinner).sub hpl.hasFDerivAt
  change HasFDerivAt (fun y => Real.log (a y i)+inner ℝ (w i) (X y)-Real.log (P y)) _ x at hright
  rw [hql.fderiv,hright.fderiv] at hd
  simpa only [smul_apply,smul_eq_mul,add_apply,sub_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,div_eq_inv_mul] using hd

 theorem selected_log_variation_nonneg {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) (v : F) :
    0≤∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
      (fderiv ℝ (fun y => Real.log (a y i)) x v) := by
  rw [selected_log_variation ha hp hA v]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (selected_pos (ha x) p i).le)

 theorem selected_exterior_apply {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) {α : ι → F → F →L[ℝ] ℝ}
    (hα : ∀ i,DifferentiableAt ℝ (α i) x) (v u : F) :
    euclideanExteriorOneForm (fun y => ∑ i,selected w (a y) p i • α i y) x v u=
      (∑ i,selected w (a x) p i * euclideanExteriorOneForm (α i) x v u)+
      ∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
        (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v) := by
  have hq (i : ι) := selected_coeff_differentiableAt (ha x) hp hA i
  have hs (i : ι) := (hq i).hasFDerivAt.smul (hα i).hasFDerivAt
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  have hs' := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hs i)
  change HasFDerivAt (fun y => ∑ i,selected w (a y) p i • α i y) _ x at hs'
  rw [hs'.fderiv]
  simp only [sum_apply,add_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem selected_exterior_positive {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) {α : ι → F → F →L[ℝ] ℝ}
    (hα : ∀ i,DifferentiableAt ℝ (α i) x) {c : ℝ} (hc : 0≤c) (v u : F)
    (hu : ∀ i,α i x u=c*(fderiv ℝ (fun y => Real.log (a y i)) x v))
    (hv : ∀ i,α i x v= -c*(fderiv ℝ (fun y => Real.log (a y i)) x u))
    (hpos : ∀ i,0<euclideanExteriorOneForm (α i) x v u) :
    0<euclideanExteriorOneForm (fun y => ∑ i,selected w (a y) p i • α i y) x v u := by
  rw [selected_exterior_apply ha hp hA hα]
  have hsum : 0<∑ i,selected w (a x) p i * euclideanExteriorOneForm (α i) x v u :=
    Finset.sum_pos (fun i _ => mul_pos (selected_pos (ha x) p i) (hpos i)) Finset.univ_nonempty
  have hnon : 0≤∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
      (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v) := by
    have he : (∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
        (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v))=
        c*((∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
          (fderiv ℝ (fun y => Real.log (a y i)) x v))+
          ∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x u)*
          (fderiv ℝ (fun y => Real.log (a y i)) x u)) := by
      rw [←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hu i,hv i]
      ring
    rw [he]
    exact mul_nonneg hc (add_nonneg (selected_log_variation_nonneg ha hp hA v)
      (selected_log_variation_nonneg ha hp hA u))
  exact add_pos_of_pos_of_nonneg hsum hnon

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold ContinuousLinearMap
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open Filter
section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem reducedPrimitive_chart (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ)
    (p : MomentPlane) (b : BaseCurve) (y : RealModel) :
    chartOneForm (reducedPrimitive w D m c p) b y=
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm y)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b y := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [chartOneForm,reducedPrimitive,reducedProbability,ContinuousLinearMap.comp_apply,sum_apply,smul_apply]

 theorem reducedForm_positive {w : ι → MomentPlane} {D m : ι → ℕ} (hm : ∀ i,m i<D i)
    {c : ℝ} (hc : 0<c) {p : MomentPlane} (hp : Surrounds w p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (reducedForm w D m c p) b y (1,0) (0,1) := by
  have hs := reducedPrimitive_smooth D m c hp
  have hsc (b : BaseCurve) : ContDiffOn ℝ ∞ (chartOneForm (reducedPrimitive w D m c p) b)
      (extChartAt 𝓘(ℝ,RealModel) b).target :=
    fun y hy => (hs.spatial_smooth 0 b hy).contDiffWithinAt
  rw [reducedForm,manifoldExteriorOneForm_chart hsc hy]
  rw [show chartOneForm (reducedPrimitive w D m c p) b=(fun z =>
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b z)
      from funext (reducedPrimitive_chart w D m c p b)]
  apply selected_exterior_positive (fun z i => coefficientNorm_pos _ _ _) hp
    (differentiableAt_pi.mpr (fun i => (coefficientNorm_chart_hasFDerivAt (D i) (m i) b hy).differentiableAt))
    (fun i => ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).differentiableAt (by simp))
    (c := c/4) (by positivity) (1,0) (0,1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).2)
  intro i
  rw [← manifoldExteriorOneForm_chart (fun b y hy =>
    ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).contDiffWithinAt) hy,
    weightedFSPrimitive_exterior]
  exact weightedFSForm_positive (hm i) hc b hy

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 def selectedProbability (w : ι → E) (D m : ι → ℕ) (p : E)
    (x : BaseCurve) (i : ι) : ℝ := selected w (fun j => coefficientNorm (D j) (m j) x) p i

 omit [FiniteDimensional ℝ E] in
 theorem selectedProbability_pos (w : ι → E) (D m : ι → ℕ) (p : E)
    (x : BaseCurve) (i : ι) : 0<selectedProbability w D m p x i :=
  selected_pos (fun j => coefficientNorm_pos (D j) (m j) x) _ _

 omit [FiniteDimensional ℝ E] in
 theorem selectedProbability_sum (w : ι → E) (D m : ι → ℕ) (p : E)
    (x : BaseCurve) : ∑ i,selectedProbability w D m p x i=1 :=
  selected_sum (fun j => coefficientNorm_pos (D j) (m j) x) _

 theorem selectedProbability_mean {w : ι → E} (D m : ι → ℕ) {p : E}
    (hp : Surrounds w p) (x : BaseCurve) : ∑ i,selectedProbability w D m p x i • w i=p :=
  selected_mean (fun j => coefficientNorm_pos (D j) (m j) x) hp

 theorem selectedProbability_smooth {w : ι → E} (D m : ι → ℕ) {p : E}
    (hp : Surrounds w p) (i : ι) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => selectedProbability w D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ι → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  exact (selected_contDiffAt (fun j => coefficientNorm_pos (D j) (m j) x) hp i).contMDiffAt.comp x
    ((ha.prodMk_space contMDiff_const).contMDiffAt)

 def selectedPrimitive (w : ι → E) (D m : ι → ℕ) (c : ℝ) (p : E) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,selectedProbability w D m p x i • weightedFSPrimitive (D i) (m i) c x

 def selectedForm (w : ι → E) (D m : ι → ℕ) (c : ℝ) (p : E) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (selectedPrimitive w D m c p)

 theorem selectedPrimitive_smooth {w : ι → E} (D m : ι → ℕ) (c : ℝ) {p : E}
    (hp : Surrounds w p) : SmoothOneFormFamily (fun _ : ℝ => selectedPrimitive w D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (selectedProbability_smooth D m hp i))
  convert hs using 1
  funext t x
  simp only [selectedPrimitive,Finset.sum_apply]

 theorem selectedForm_smooth {w : ι → E} (D m : ι → ℕ) (c : ℝ) {p : E}
    (hp : Surrounds w p) : SmoothTwoForm (selectedForm w D m c p) :=
  (manifoldExteriorOneForm_family_smooth (selectedPrimitive_smooth D m c hp)).eval 0

 omit [Nonempty ι] [FiniteDimensional ℝ E] in
 theorem selectedForm_skew (w : ι → E) (D m : ι → ℕ) (c : ℝ) (p : E)
    (x : BaseCurve) (v u : RealModel) : selectedForm w D m c p x v u= -selectedForm w D m c p x u v :=
  manifoldExteriorOneForm_skew _ _ _ _

 omit [Nonempty ι] [FiniteDimensional ℝ E] in
 theorem selectedPrimitive_chart (w : ι → E) (D m : ι → ℕ) (c : ℝ)
    (p : E) (b : BaseCurve) (y : RealModel) :
    chartOneForm (selectedPrimitive w D m c p) b y=
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm y)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b y := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [chartOneForm,selectedPrimitive,selectedProbability,ContinuousLinearMap.comp_apply,sum_apply,smul_apply]

 theorem selectedForm_positive {w : ι → E} {D m : ι → ℕ} (hm : ∀ i,m i<D i)
    {c : ℝ} (hc : 0<c) {p : E} (hp : Surrounds w p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (selectedForm w D m c p) b y (1,0) (0,1) := by
  have hs := selectedPrimitive_smooth D m c hp
  have hsc (b : BaseCurve) : ContDiffOn ℝ ∞ (chartOneForm (selectedPrimitive w D m c p) b)
      (extChartAt 𝓘(ℝ,RealModel) b).target :=
    fun y hy => (hs.spatial_smooth 0 b hy).contDiffWithinAt
  rw [selectedForm,manifoldExteriorOneForm_chart hsc hy]
  rw [show chartOneForm (selectedPrimitive w D m c p) b=(fun z =>
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b z)
      from funext (selectedPrimitive_chart w D m c p b)]
  apply selected_exterior_positive (fun z i => coefficientNorm_pos _ _ _) hp
    (differentiableAt_pi.mpr (fun i => (coefficientNorm_chart_hasFDerivAt (D i) (m i) b hy).differentiableAt))
    (fun i => ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).differentiableAt (by simp))
    (c := c/4) (by positivity) (1,0) (0,1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).2)
  intro i
  rw [← manifoldExteriorOneForm_chart (fun b y hy =>
    ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).contDiffWithinAt) hy,
    weightedFSPrimitive_exterior]
  exact weightedFSForm_positive (hm i) hc b hy

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem face_surrounds {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    {B : ℕ} (hB : ∃ i,k i=(0,B)) {p : ℝ} (hp : 0<p ∧ p<B) :
    Surrounds (faceWeight k) p := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨iB,hiB⟩ := hB
  exact interval_surrounds
    ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
    ⟨⟨iB,by simp [hiB]⟩,by simp [faceWeight,hiB]⟩ hp

theorem inverse_axis {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) :
    nonnegativeInverse k a (0,p)=(0,Real.exp (inverse (faceWeight k) (fun i => a i.val) p)) := by
  obtain ⟨i0,hi0⟩ := h0
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  apply nonnegativeInverse_eq_of_moment ha ⟨i0,hi0⟩ he0 he1
    ⟨le_rfl,(Real.exp_pos _).le⟩
  rw [moment_face_exp,inverse_spec (fun i => ha i.val) hp]

theorem probability_axis_active (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) (i : Face k) :
    probability k a (0,Real.exp x) i.val=gibbs (faceWeight k) (fun j => a j.val) x i := by
  rw [probability,polynomial_face_exp]
  simp [monomial, i.property,gibbs,faceWeight,← Real.exp_nat_mul,mul_comm]

theorem probability_axis_inactive {k : ι → ℕ × ℕ} (a : ι → ℝ) (t : ℝ) {i : ι}
    (hi : (k i).1≠0) : probability k a (0,t) i=0 := by
  simp [probability,monomial_axis,hi]

theorem selected_axis_active {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) (i : Face k) :
    selected k a (0,p) i.val=FiniteMoment.selected (faceWeight k) (fun j => a j.val) p i := by
  unfold selected
  rw [inverse_axis ha h0 he0 he1 hp,probability_axis_active]
  rfl

theorem selected_axis_inactive {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) {i : ι} (hi : (k i).1≠0) :
    selected k a (0,p) i=0 := by
  unfold selected
  rw [inverse_axis ha h0 he0 he1 hp]
  exact probability_axis_inactive a _ hi

theorem probability_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) (i : ι) :
    probability (fun j => (k j).swap) a r.swap i=probability k a r i := by
  rw [probability,polynomial_swap,probability]
  simp only [monomial,Prod.fst_swap,Prod.snd_swap,mul_comm]

theorem nonnegativeInverse_swap {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : ∃ r : Plane,(0≤r.1 ∧ 0≤r.2) ∧ moment k a r=p) :
    nonnegativeInverse (fun j => (k j).swap) a p.swap=(nonnegativeInverse k a p).swap := by
  have h0' : ∃ i,(k i).swap=(0,0) := by obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by obtain ⟨i,hi⟩ := he1; exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
  apply nonnegativeInverse_eq_of_moment ha h0' he0' he1'
    ⟨(nonnegativeInverse_nonneg k a p).2,(nonnegativeInverse_nonneg k a p).1⟩
  rw [moment_swap,nonnegativeInverse_spec hp]

theorem selected_swap {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : ∃ r : Plane,(0≤r.1 ∧ 0≤r.2) ∧ moment k a r=p) (i : ι) :
    selected (fun j => (k j).swap) a p.swap i=selected k a p i := by
  unfold selected
  rw [nonnegativeInverse_swap ha h0 he0 he1 hp,probability_swap]

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

def radialProbability (k : ι → ℕ × ℕ) (D m : ι → ℕ) (p : Radial.Plane)
    (x : BaseCurve) (i : ι) : ℝ :=
  Radial.selected k (fun j => coefficientNorm (D j) (m j) x) p i

def radialPrimitive (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,radialProbability k D m p x i • weightedFSPrimitive (D i) (m i) c x

def radialForm (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (radialPrimitive k D m c p)

theorem radialProbability_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => radialProbability Radial.latticeIndex D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  have hs := Radial.trapezoid_selected_coeff_contDiffAt hA hAB
    (fun j => coefficientNorm_pos (D j) (m j) x) hp i
  have hc := hs.contMDiffAt.comp x ha.contMDiffAt
  exact hc

theorem radialPrimitive_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) :
    SmoothOneFormFamily (fun _ : ℝ => radialPrimitive Radial.latticeIndex D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (radialProbability_smooth hA hAB D m hp i))
  convert hs using 1
  funext t x
  simp only [radialPrimitive,Finset.sum_apply]

theorem radialForm_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) : SmoothTwoForm (radialForm Radial.latticeIndex D m c p) :=
  (manifoldExteriorOneForm_family_smooth (radialPrimitive_smooth hA hAB D m c hp)).eval 0

theorem radialForm_skew (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (x : BaseCurve) (v u : RealModel) : radialForm k D m c p x v u= -radialForm k D m c p x u v :=
  manifoldExteriorOneForm_skew _ _ _ _

theorem radialPrimitive_eq_reduced [Nonempty ι] {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : Surrounds (Radial.weight k) (planeVector p.1 p.2)) :
    radialPrimitive k D m c p=reducedPrimitive (Radial.weight k) D m c (planeVector p.1 p.2) := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [radialProbability,Radial.selected_eq_exponential
    (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp]
  rfl

theorem radialPrimitive_eq_face {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : ℝ} (hp : Surrounds (Radial.faceWeight k) p) :
    radialPrimitive k D m c (0,p)=selectedPrimitive (Radial.faceWeight k)
      (fun i => D i.val) (fun i => m i.val) c p := by
  classical
  funext x
  change (∑ i,Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
    weightedFSPrimitive (D i) (m i) c x)=_
  have he : (∑ i,Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
      weightedFSPrimitive (D i) (m i) c x)=
      ∑ i,if (k i).1=0 then Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
        weightedFSPrimitive (D i) (m i) c x else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (k i).1=0
    · simp [hi]
    · simp [hi,Radial.selected_axis_inactive (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp hi]
  rw [he,← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := fun i => (k i).1=0) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Radial.selected_axis_active (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp]
  rfl

end PackingSufficiencySupport.CubicModel
end

end OAI
