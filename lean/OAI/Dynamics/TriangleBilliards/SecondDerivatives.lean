import OAI.Dynamics.TriangleBilliards.FourierEnergy

namespace OAI

universe uA uE uF uG uIota

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section

namespace TriangularBilliards
open Analysis
open MeasureTheory Filter
open scoped ComplexConjugate NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma seam_rotationalCR {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
      (hf.toLp f) ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)) := by
  intro θ
  obtain ⟨h₁,h₂⟩ := seam_rotated_generators hs hd hC hf hx hy θ
  simp only [fourier_neg, fourier_one,
    map_smul, map_sub, map_add]
  constructor
  · rw [← real_parts_CR_algebra, Complex.coe_smul, Complex.coe_smul]
    exact h₁
  · rw [← imag_parts_CR_algebra, Complex.coe_smul, Complex.coe_smul]
    exact h₂

/-- The second spatial jet on the actual smooth seam core. No spectral
regularity of an invariant is assumed in this lemma. -/
lemma seam_projected_CR_norms {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C Cx Cy : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hCx : ∀ x v b, ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ Cx)
    (hCy : ∀ x v b, ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ Cy)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (hxx : MemLp (xDerivative (xDerivative f)) 2 (doubleMeasure Q))
    (hxy : MemLp (xDerivative (yDerivative f)) 2 (doubleMeasure Q))
    (hyy : MemLp (yDerivative (yDerivative f)) 2 (doubleMeasure Q))
    (j : ℤ) :
    ‖(angularCircleAction Q).projection (j+1)
      ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))‖ =
    ‖(angularCircleAction Q).projection (j-1)
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have he : xDerivative (yDerivative f) = yDerivative (xDerivative f) :=
    funext (x_y_commute hd)
  have hyx : MemLp (yDerivative (xDerivative f)) 2 (doubleMeasure Q) := by rwa [← he]
  have heLp : hyx.toLp _ = hxy.toLp _ :=
    MemLp.toLp_congr hyx hxy (Filter.Eventually.of_forall (congrFun he.symm))
  have h := seam_rotationalCR hs hd' hC hf hx hy
  have hₓ := seam_rotationalCR (hs.xDerivative hd')
    (fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)) hCx hx hxx hyx
  have hᵧ := seam_rotationalCR (hs.yDerivative hd')
    (fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)) hCy hy hxy hyy
  rw [heLp] at hₓ
  let aa := (1/4 : ℂ) • (hxx.toLp _ - (2 * Complex.I) • hxy.toLp _ - hyy.toLp _)
  let c := (1/4 : ℂ) • (hxx.toLp _ + hyy.toLp _)
  let bb := (1/4 : ℂ) • (hxx.toLp _ + (2 * Complex.I) • hxy.toLp _ - hyy.toLp _)
  have ha : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)) aa c := by
    have hh := (hₓ.add (hᵧ.smul (-Complex.I))).smul (1/2)
    convert hh using 1
    · module
    · dsimp [aa]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
    · dsimp [c]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
  have hb : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)) c bb := by
    have hh := (hₓ.add (hᵧ.smul Complex.I)).smul (1/2)
    convert hh using 1
    · dsimp [c]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
    · dsimp [bb]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
  exact h.projected_norm_eq ha hb j

end TriangularBilliards

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

namespace TriangularBilliards.Analysis

variable {E : Type uE} {F : Type uF} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma convolution_uniform_bound (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f) {C : ℝ}
    (hg : ∀ z, ‖g z‖ ≤ C) (x : ℂ) :
    ‖MeasureTheory.convolution (𝕜 := ℝ) f g L volume x‖ ≤ ‖L‖ * (∫ y, ‖f y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hg 0)
  unfold MeasureTheory.convolution
  calc
    _ ≤ ∫ y, ‖L (f y) (g (x-y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖L‖ * ‖f y‖ * C := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        ((hf.norm.const_mul _).mul_const _)
      filter_upwards [] with y
      exact (L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hg _) (by positivity))
    _ = _ := by rw [integral_mul_const, integral_const_mul]

lemma convolution_fderiv_eq (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume) =
      MeasureTheory.convolution (𝕜 := ℝ) f (fderiv ℝ g) (L.precompR ℂ) volume := by
  funext y
  exact (hgc.hasFDerivAt_convolution_right L hf.locallyIntegrable
    (hg.of_le (by simp)) y).fderiv

lemma convolution_second_formula (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    fderiv ℝ (fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume)) =
      MeasureTheory.convolution (𝕜 := ℝ) f (fderiv ℝ (fderiv ℝ g)) ((L.precompR ℂ).precompR ℂ) volume := by
  rw [convolution_fderiv_eq L hf hg hgc]
  exact convolution_fderiv_eq (L.precompR ℂ) hf (hg.fderiv_right (by simp)) (hgc.fderiv ℝ)

lemma compact_second_bound {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C := by
  have hc₁ : HasCompactSupport (fderiv ℝ g) := HasCompactSupport.fderiv (f := g) ℝ hgc
  have hc : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
    HasCompactSupport.fderiv (f := fderiv ℝ g) ℝ hc₁
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hd' : Continuous (fderiv ℝ (fderiv ℝ g)) := hd.continuous_fderiv (by simp)
  exact HasCompactSupport.exists_bound_of_continuous (f := fderiv ℝ (fderiv ℝ g)) hc hd'

/-- Uniform second jets with an abstract kernel codomain. -/
lemma convolution_second_bound (L : E →L[ℝ] F →L[ℝ] G)
    {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → E), Integrable f → ∀ x,
      ‖fderiv ℝ (fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume)) x‖ ≤ C * (∫ y, ‖f y‖) := by
  obtain ⟨D,hD⟩ := compact_second_bound hg hgc
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] G) := inferInstance
  let : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] G) := inferInstance
  let K := (L.precompR ℂ).precompR ℂ
  refine ⟨‖K‖ * D, mul_nonneg (norm_nonneg K)
    ((norm_nonneg (fderiv ℝ (fderiv ℝ g) 0)).trans (hD 0)), ?_⟩
  intro f hf x
  rw [convolution_second_formula L hf hg hgc]
  have hh := convolution_uniform_bound K hf hD x
  convert hh using 1
  exact mul_right_comm _ D _

/-- Joint measurability of a spatial directional derivative requires no
angular differentiability or continuity. -/
lemma measurable_directional_derivative {A : Type uA} [MeasurableSpace A]
    {f : ℂ × A → ℂ} (hf : Measurable f)
    (hd : ∀ a, Differentiable ℝ (fun x => f (x,a)))
    {v : A → ℂ} (hv : Measurable v) :
    Measurable (fun z : ℂ × A => fderiv ℝ (fun x => f (x,z.2)) z.1 (v z.2)) := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    change 1 / ((n : ℝ) + 1) ≠ 0
    positivity
  apply measurable_of_tendsto_metrizable
    (f := fun n z => (t n)⁻¹ • (f (z.1 + t n • v z.2, z.2) - f z))
  · intro n
    exact (measurable_const : Measurable (fun _ : ℂ × A => (t n)⁻¹)).smul ((hf.comp
      ((measurable_fst.add ((measurable_const : Measurable (fun _ : ℂ × A => t n)).smul (hv.comp measurable_snd))).prodMk measurable_snd)).sub hf)
  · apply tendsto_pi_nhds.mpr
    intro z
    have hline : HasDerivAt (fun r : ℝ => z.1 + r • v z.2) (v z.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v z.2)).const_add z.1
    have hf' : HasFDerivAt (fun x => f (x,z.2)) (fderiv ℝ (fun x => f (x,z.2)) z.1)
        (z.1 + (0 : ℝ) • v z.2) := by simpa using (hd z.2 z.1).hasFDerivAt
    have hh := (hf'.comp_hasDerivAt 0 hline).tendsto_slope_zero.comp ht
    simpa only [Function.comp_def, zero_add, zero_smul, add_zero] using hh

lemma second_bound_comp_constant_derivative {f : ℂ → G} {r : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (A : ℂ →L[ℝ] ℂ)
    (hr : ∀ x, HasFDerivAt r A x) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ r)) x‖ ≤
      ‖(ContinuousLinearMap.compL ℝ ℂ ℂ G).flip A‖ * C * ‖A‖ := by
  let J := (ContinuousLinearMap.compL ℝ ℂ ℂ G).flip A
  have he : fderiv ℝ (f ∘ r) = fun y => J (fderiv ℝ f (r y)) := by
    funext y
    exact (((hf.differentiable (by simp)) (r y)).hasFDerivAt.comp y (hr y)).fderiv
  have hd : HasFDerivAt (fun y => J (fderiv ℝ f (r y)))
      (J.comp ((fderiv ℝ (fderiv ℝ f) (r x)).comp A)) x :=
    J.hasFDerivAt.comp x (((hf.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) (r x)).hasFDerivAt.comp x (hr x))
  rw [he, hd.fderiv]
  calc
    _ ≤ ‖J‖ * (‖fderiv ℝ (fderiv ℝ f) (r x)‖ * ‖A‖) :=
      (J.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC (r x)) (norm_nonneg _)) (norm_nonneg A)

lemma norm_second_eq_iterated (f : ℂ → G) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

lemma second_bound_smul {a : ℂ → ℝ} {f : ℂ → G}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    {A₀ A₁ A₂ C₀ C₁ C₂ : ℝ}
    (hA₀ : ∀ x, ‖a x‖ ≤ A₀) (hA₁ : ∀ x, ‖fderiv ℝ a x‖ ≤ A₁)
    (hA₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ A₂)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀) (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (fun y => a y • f y)) x‖ ≤ A₀*C₂ + 2*A₁*C₁ + A₂*C₀ := by
  have hh := norm_iteratedFDeriv_smul_le ha hf x (n := 2) (by norm_cast)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, Nat.sub_zero, Nat.reduceSub, one_mul,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one,
    ← norm_second_eq_iterated] at hh
  apply hh.trans
  apply add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul (hA₀ x) (hC₂ x) (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)) ((norm_nonneg (a x)).trans (hA₀ x))
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (hA₁ x) (by norm_num)) (hC₁ x)
      (norm_nonneg _) (by have := (norm_nonneg _).trans (hA₁ x); positivity)
  · exact mul_le_mul (hA₂ x) (hC₀ x) (norm_nonneg (f x)) ((norm_nonneg (fderiv ℝ (fderiv ℝ a) x)).trans (hA₂ x))

lemma second_add {f g : ℂ → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y + g y) = fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
  rw [he]
  exact fderiv_add ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma second_sum {ι : Type uIota} (s : Finset ι) {f : ι → ℂ → G}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ i ∈ s, f i y)) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) x := by
  have he : fderiv ℝ (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, fderiv ℝ (f i) y := by
    funext y
    exact fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) y)
  rw [he]
  exact fderiv_fun_sum (fun i hi => ((hf i hi).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma directional_derivative_bound {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (v x : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y v) x‖ ≤ C * ‖v‖ := by
  have hd := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x).hasFDerivAt
  have he : fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    simpa using (hd.clm_apply (hasFDerivAt_const v x)).fderiv
  rw [he]
  exact ((by simpa only [ContinuousLinearMap.opNorm_flip] using
      ((fderiv ℝ (fderiv ℝ f) x).flip.le_opNorm v)) : ‖(fderiv ℝ (fderiv ℝ f) x).flip v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖).trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg v))

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma vertexCutoff_sub_one_compact (Q : Triangle) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun x => vertexCutoff Q R x - 1) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_iUnion (fun i : Fin 3 => isCompact_closedBall (Q.vertex i) (2*R)))
  intro x hx
  by_contra hn
  have hfar (i : Fin 3) : 2*R ≤ ‖x - Q.vertex i‖ := by
    have hh : x ∉ Metric.closedBall (Q.vertex i) (2*R) := fun hi => hn (mem_iUnion.mpr ⟨i,hi⟩)
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh)).le
  have he : vertexCutoff Q R x = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact vertexCutoffFactor_one Q hR i (hfar i)
  exact hx (by change vertexCutoff Q R x - 1 = 0; rw [he, sub_self])

lemma vertexCutoff_second_bound (Q : Triangle) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ (vertexCutoff Q R)) x‖ ≤ C := by
  have hc := vertexCutoff_sub_one_compact Q hR
  have hd := (vertexCutoff_contDiff Q R).sub (contDiff_const (c := (1 : ℝ)))
  have he : fderiv ℝ (fun x => vertexCutoff Q R x - 1) = fderiv ℝ (vertexCutoff Q R) := by
    funext x
    exact fderiv_sub_const (x := x) 1
  obtain ⟨C,hC⟩ := compact_second_bound hd hc
  exact ⟨C, by simpa only [he] using hC⟩

lemma spatialSlice_integral_norm_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) :
    (∫ x, ‖spatialSlice Q f b v x‖) ≤ (volume Q.table).toReal * H := by
  have hi := bounded_spatialSlice_integrable Q hm hf v b
  let : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  rw [spatialSlice]
  simp only [norm_indicator_eq_indicator_norm]
  rw [integral_indicator Q.measurableSet_table]
  calc
    _ ≤ ∫ _x in Q.table, H := integral_mono_ae hi.norm (integrable_const H) (Filter.Eventually.of_forall (fun x => hf ((x,v),b)))
    _ = _ := by simp [Measure.real, smul_eq_mul]

lemma directS_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ, ∀ x v b, ‖fderiv ℝ (fderiv ℝ (directS Q ε f b v)) x‖ ≤ C := by
  obtain ⟨C,hCp,hC⟩ := convolution_second_bound scalarKernelMap (kernel_contDiff ε) (kernel_hasCompactSupport hε)
  refine ⟨C * ((volume Q.table).toReal * H), fun x v b => ?_⟩
  rw [directS_eq_convolution]
  apply (hC _ ((integrable_indicator_iff Q.measurableSet_table).mpr
    (bounded_spatialSlice_integrable Q hm hf v b)) x).trans
  exact mul_le_mul_of_nonneg_left (spatialSlice_integral_norm_bound Q hm hf v b) hCp

lemma reflectedS_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H)
    (i : Fin 3) :
    ∃ C : ℝ, ∀ x v b, ‖fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := directS_second_bound Q hε hm hf
  let A := (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨‖(ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip A‖ * C * ‖A‖, fun x v b => ?_⟩
  rw [reflectedS_eq_directS]
  exact second_bound_comp_constant_derivative (directS_contDiff Q hε
    (bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1))) A
    (wallReflection_hasFDerivAt Q i) (fun x => hC x _ _) x

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma reflectedSmoothing_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ, ∀ x v b,
      ‖fderiv ℝ (fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,v),b))) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := directS_second_bound Q hε hm hf
  choose D hD using fun i : Fin 3 => reflectedS_second_bound Q hε hm hf i
  refine ⟨C + ∑ i : Fin 3, D i, fun x v b => ?_⟩
  have hd := directS_contDiff Q hε (bounded_spatialSlice_integrable Q hm hf v b)
  have hr (i : Fin 3) := reflectedS_contDiff Q i hε
    (bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1))
  change ‖fderiv ℝ (fderiv ℝ (fun y => directS Q ε f b v y + ∑ i : Fin 3, reflectedS Q i ε f b v y)) x‖ ≤ _
  rw [second_add hd (ContDiff.sum (fun i _ => hr i)), second_sum Finset.univ (fun i _ => hr i)]
  have hh : ‖∑ i : Fin 3, fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x‖ ≤ ∑ i : Fin 3, D i :=
    (norm_sum_le Finset.univ (fun i : Fin 3 => fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x)).trans
      (Finset.sum_le_sum (fun i _ => hD i x v b))
  apply (norm_add_le (fderiv ℝ (fderiv ℝ (directS Q ε f b v)) x)
    (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x)).trans
  exact add_le_add (hC x v b) hh

lemma supportedSmoothing_second_bound (Q : Triangle) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ≥0, ∀ x v b,
      ‖fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b))) x‖ ≤ C := by
  obtain ⟨A,hAp,hA⟩ := exists_vertexCutoff_derivative_bound
  obtain ⟨B,hB⟩ := vertexCutoff_second_bound Q hR
  obtain ⟨C,hC⟩ := reflectedSmoothing_second_bound Q hε hm hf
  have hH : 0 ≤ H := (norm_nonneg (f ((0,1),0))).trans (hf _)
  let M := 1*C + 2*(A/R)*(4*derivativeMass*H/ε) + B*(4*H)
  have hM (x : ℂ) (v : Circle) (b : ZMod 2) :
      ‖fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b))) x‖ ≤ M := by
    apply second_bound_smul (vertexCutoff_contDiff Q R)
      (reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hm hf v b)
        (fun i => bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1)))
    · intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R y).1]
      exact (vertexCutoff_mem_Icc Q R y).2
    · exact hA Q R hR
    · exact hB
    · intro y
      exact reflectedSmoothing_norm_bound Q hε hH hf ((y,v),b)
    · intro y
      rw [(reflectedSmoothing_hasFDerivAt Q hε hm
        (bounded_spatialSlice_integrable Q hm hf v b)
        (fun i => bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1)) y).fderiv]
      exact reflectedSmoothingGradient_norm_bound Q hε hH hf ((y,v),b)
    · intro y
      exact hC y v b
  exact ⟨⟨M, (norm_nonneg (fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,1),0))) 0)).trans (hM 0 1 0)⟩, hM⟩

lemma xDerivative_measurable {f : DoublePhase → ℂ} (hm : Measurable f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) : Measurable (xDerivative f) := by
  have hh := measurable_directional_derivative
    (f := fun z : ℂ × (Circle × ZMod 2) => f ((z.1,z.2.1),z.2.2))
    (hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
    (fun a => hd a.1 a.2) (v := fun a => (a.1 : ℂ))
    ((show Continuous (fun a : Circle × ZMod 2 => (a.1 : ℂ)) from continuous_subtype_val.comp continuous_fst).measurable)
  exact hh.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma yDerivative_measurable {f : DoublePhase → ℂ} (hm : Measurable f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) : Measurable (yDerivative f) := by
  have hh := measurable_directional_derivative
    (f := fun z : ℂ × (Circle × ZMod 2) => f ((z.1,z.2.1),z.2.2))
    (hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
    (fun a => hd a.1 a.2) (v := fun a => transverseVelocity a.1 a.2)
    (by
      unfold transverseVelocity
      exact (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
        measurable_const measurable_const).mul
        (show Continuous (fun a : Circle × ZMod 2 => (a.1 : ℂ)) from
          continuous_subtype_val.comp continuous_fst).measurable)
  exact hh.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end TriangularBilliards

namespace TriangularBilliards
open Analysis MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma norm_transverseVelocity (v : Circle) (b : ZMod 2) : ‖transverseVelocity v b‖ = 1 := by
  unfold transverseVelocity
  split <;> simp [Circle.norm_coe]

lemma xDerivative_fderiv_bound {f : DoublePhase → ℂ}
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) {C : ℝ}
    (hC : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ C)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ C := by
  simpa only [xDerivative, Circle.norm_coe, mul_one] using
    directional_derivative_bound (hd v b) (fun y => hC y v b) (v : ℂ) x

lemma yDerivative_fderiv_bound {f : DoublePhase → ℂ}
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) {C : ℝ}
    (hC : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ C)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ C := by
  simpa only [yDerivative, norm_transverseVelocity, mul_one] using
    directional_derivative_bound (hd v b) (fun y => hC y v b) (transverseVelocity v b) x

lemma xDerivative_memLp_of_gradient_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : Measurable f) (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    MemLp (xDerivative f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (xDerivative_measurable hm hd).aestronglyMeasurable C
  filter_upwards [] with z
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [Circle.norm_coe, mul_one]
    exact hC z.1.1 z.1.2 z.2)

lemma yDerivative_memLp_of_gradient_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : Measurable f) (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    MemLp (yDerivative f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (yDerivative_measurable hm hd).aestronglyMeasurable C
  filter_upwards [] with z
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [norm_transverseVelocity, mul_one]
    exact hC z.1.1 z.1.2 z.2)

lemma seam_projected_CR_norms_of_bounded_jets {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q)) (j : ℤ) :
    let hx := xDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let hy := yDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    ‖(angularCircleAction Q).projection (j+1)
      ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))‖ =
    ‖(angularCircleAction Q).projection (j-1)
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ := by
  dsimp only
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hmx := xDerivative_measurable hm hd'
  have hmy := yDerivative_measurable hm hd'
  have hx' := fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)
  have hy' := fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)
  have hX := xDerivative_fderiv_bound hd hD
  have hY := yDerivative_fderiv_bound hd hD
  exact seam_projected_CR_norms hs hd hC hX hY hf _ _
    (xDerivative_memLp_of_gradient_bound Q hmx hx' hX)
    (xDerivative_memLp_of_gradient_bound Q hmy hy' hY)
    (yDerivative_memLp_of_gradient_bound Q hmy hy' hY) j

end TriangularBilliards

end
end
end
end
end
end
end
end

end OAI
