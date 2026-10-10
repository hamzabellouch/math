import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CanonicalCutoffWave
import OAI.Geometry.SmoothYau.Geometry.WaveDerivCompLinear
import OAI.Geometry.SmoothYau.Limits.FrameDualNorm
import OAI.Geometry.SmoothYau.Smoothness.FlowInitialFderiv

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalFamilyVecNorm : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance normalFamilyVecSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance normalFamilyBiVecNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalFamilyBiVecSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalFamilyDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma contDiff_frameChristoffel (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => (metricChristoffel g q.1).comp q.2) :=
    ((contDiff_metricChristoffel g).comp contDiff_fst).clm_comp contDiff_snd
  have h2 := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h1
  have h3 := h2.clm_comp contDiff_snd
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h3

lemma contDiff_normalJetFamily (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => (metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) :=
    (contDiff_frameChristoffel g).comp contDiff_fst
  exact (contDiff_fst.fst.add (contDiff_fst.snd.clm_apply contDiff_snd)).sub
    ((hC.clm_apply contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

lemma contDiff_normalMetricFamily_apply (g : SmoothMetric E E) (v w : E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalMetricTensor g q.1.1 q.1.2 q.2 v w) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) :=
    ((contDiff_frameChristoffel g).comp contDiff_fst).clm_apply contDiff_snd
  have hD := (show ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => q.1.2) from contDiff_fst.snd).sub hC
  exact (((contDiff_selfMetricFlat g).comp (contDiff_normalJetFamily g)).clm_apply
    (hD.clm_apply contDiff_const)).clm_apply (hD.clm_apply contDiff_const)

theorem compact_normal_coordinate_radius [Nontrivial E] (g : SmoothMetric E E)
    {K : Set E} (hK : IsCompact K) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ q ∈ metricFrameSet g K,
      ∃ e : OpenPartialHomeomorph E E,
        (e : E → E) = normalJetMap q.1 q.2
          ((metricChristoffel g q.1).bilinearComp q.2 q.2) ∧
        e.source = Metric.ball 0 r ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨R,hR,hRb⟩ := metricFrameSet_inverse_bound g hK
  obtain ⟨B,hBb⟩ := (metricFrameSet_isCompact g hK).exists_bound_of_continuousOn
    (f := fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2)
    (contDiff_frameChristoffel g).continuous.continuousOn
  let r : ℝ≥0 := ⟨(2*(R+1)*(max B 0+1))⁻¹, by positivity⟩
  have hr : 0 < r := by change 0 < (2*(R+1)*(max B 0+1))⁻¹; positivity
  refine ⟨r,hr,?_⟩
  intro q hq
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  let C := (metricChristoffel g q.1).bilinearComp q.2 q.2
  have hAi : (A.symm : E →L[ℝ] E) = q.2.inverse := by
    rw [←hA, ContinuousLinearMap.inverse_equiv]
  have hAiPos : 0 < ‖(A.symm : E →L[ℝ] E)‖₊ := by
    rw [nnnorm_pos]
    intro hz
    obtain ⟨v,hv⟩ := exists_ne (0 : E)
    have hh := congrArg (fun T : E →L[ℝ] E => T (A v)) hz
    simp only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply, _root_.zero_apply] at hh
    exact hv hh
  have hb : ‖(A.symm : E →L[ℝ] E)‖ * (‖C‖ * (r : ℝ)) < 1 := by
    have hi : ‖(A.symm : E →L[ℝ] E)‖ ≤ R := by rw [hAi]; exact hRb q hq
    have hc : ‖C‖ ≤ max B 0 := (hBb q hq).trans (le_max_left _ _)
    have hm : ‖(A.symm : E →L[ℝ] E)‖ * (‖C‖ * (r : ℝ)) ≤
        R * (max B 0 * (2*(R+1)*(max B 0+1))⁻¹) := by
      change ‖(A.symm : E →L[ℝ] E)‖ * (‖C‖ * (2*(R+1)*(max B 0+1))⁻¹) ≤ _
      gcongr
    apply lt_of_le_of_lt hm
    rw [←mul_assoc, ←div_eq_mul_inv, div_lt_one (by positivity)]
    nlinarith [le_max_right B 0]
  have hsmall : ‖C‖₊ * r < ‖(A.symm : E →L[ℝ] E)‖₊⁻¹ := by
    have hnn : ‖(A.symm : E →L[ℝ] E)‖₊ * (‖C‖₊ * r) < 1 := by exact_mod_cast hb
    simpa only [mul_one] using (lt_inv_mul_iff₀ hAiPos).mpr hnn
  obtain ⟨e,he,hs,hi⟩ := normalJetMap_uniform_inverse q.1 A C
    (fun v w => metricChristoffel_symm g q.1 (q.2 v) (q.2 w)) r hsmall
  exact ⟨e, by simpa only [hA] using he, hs, hi⟩

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma normal_iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma parameter_iteratedFDeriv (f : P × E → F) (t : P) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let q : P × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : P × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := normal_iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_parameter_iteratedFDeriv (f : P × E → F) {z : P × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : P × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact parameter_iteratedFDeriv f w.1 w.2 n hw


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
section ParameterDerivative
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma parameter_fderiv_apply (f : P × E → F) (hf : Differentiable ℝ f)
    (p : P) (x v : E) :
    fderiv ℝ (fun y => f (p,y)) x v = fderiv ℝ f (p,x) (0,v) := by
  have h := (hf (p,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun T => T v) h.fderiv

lemma contDiff_parameter_fderiv_apply (f : P × E → F) (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun q : P × E => fderiv ℝ (fun x => f (q.1,x)) q.2 v) := by
  simp only [parameter_fderiv_apply f (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma continuous_parameter_iteratedFDeriv (f : P × E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ k (fun x => f (q.1,x)) q.2) :=
  continuous_iff_continuousAt.mpr (fun _ => continuousAt_parameter_iteratedFDeriv f k hf.contDiffAt)
end ParameterDerivative

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]
lemma contDiff_matrix_det (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) :
    ContDiff ℝ ∞ (fun p => (A p).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hA _ _

lemma contDiff_matrix_adjugate (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun p => (A p).adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hA _ _

lemma contDiffOn_matrix_inv (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiffOn ℝ ∞ (fun p => (A p)⁻¹ i j) {p | (A p).det ≠ 0} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_matrix_det A hA).contDiffOn.inv (fun _ hp => hp)).mul
    (contDiff_matrix_adjugate A hA i j).contDiffOn

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
abbrev NormalWaveSpace := EuclideanSpace ℝ (Fin 3)
abbrev NormalWaveParameter := NormalWaveSpace × (NormalWaveSpace →L[ℝ] NormalWaveSpace)

def normalWaveMetric (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : NormalWaveSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => normalMetricTensor g q.1 q.2 x
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma contDiff_normalWaveMetric (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun q : NormalWaveParameter × NormalWaveSpace => normalWaveMetric g q.1 q.2 i j) :=
  contDiff_normalMetricFamily_apply g _ _

lemma normalWaveMetric_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    normalWaveMetric g q 0 = 1 := by
  ext i j
  change normalMetricTensor g q.1 q.2 0 _ _ = _
  rw [normalMetricTensor_at_zero]
  change selfMetricFlat g q.1 (q.2 _) (q.2 _) = _
  rw [hq.2]
  exact (EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite i j

lemma normalWaveMetric_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) : HasFDerivAt (𝕜 := ℝ) (normalWaveMetric g q) 0 0 := by
  have hc (i j : Fin 3) : HasFDerivAt (𝕜 := ℝ) (fun x => normalWaveMetric g q x i j) 0 0 := by
    have h := (contDiff_normalMetricTensor_apply g q.1 q.2
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)).differentiable (by simp) 0
    simpa only [normalWaveMetric, normalMetricTensor_normal_jet] using h.hasFDerivAt
  convert (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_pi.mpr (fun j => hc i j))) using 1 <;> rfl

lemma hasFDerivAt_matrix_inv_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix ι ι ℝ) {x : E} (hA : HasFDerivAt (𝕜 := ℝ) A 0 x) (hdet : (A x).det ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun y => (A y)⁻¹) 0 x := by
  have hc (i j : ι) : ContDiffAt ℝ ∞ (fun M : Matrix ι ι ℝ => M⁻¹ i j) (A x) := by
    have hO : IsOpen {M : Matrix ι ι ℝ | M.det ≠ 0} :=
      isOpen_ne_fun (contDiff_matrix_det id (fun _ _ => by fun_prop)).continuous continuous_const
    exact (contDiffOn_matrix_inv id (fun _ _ => by fun_prop) i j _ hdet).contDiffAt
      (hO.mem_nhds hdet)
  have hi : DifferentiableAt ℝ (fun M : Matrix ι ι ℝ => M⁻¹) (A x) := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hc i j).differentiableAt (by simp)
  have h := hi.hasFDerivAt.comp x hA
  erw [ContinuousLinearMap.comp_zero] at h
  exact h

lemma normalWaveInverse_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    HasFDerivAt (𝕜 := ℝ) (fun x => (normalWaveMetric g q x)⁻¹) 0 0 :=
  hasFDerivAt_matrix_inv_zero _ (normalWaveMetric_first_jet g q) (by rw [normalWaveMetric_zero g hq]; simp)

theorem exists_normal_inverse_extension (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ,
      ∃ d : NormalWaveParameter × NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ d ∧
      ∃ O : Set (NormalWaveParameter × NormalWaveSpace), IsOpen O ∧
        metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ O ∧
        ∀ q ∈ O, A q = (normalWaveMetric g q.1 q.2)⁻¹ ∧
          d q = (normalWaveMetric g q.1 q.2).det⁻¹ := by
  let G := fun q : NormalWaveParameter × NormalWaveSpace => normalWaveMetric g q.1 q.2
  let V := {q | (G q).det ≠ 0}
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun q => G q i j) := contDiff_normalWaveMetric g i j
  have hV : IsOpen V := isOpen_ne_fun (contDiff_matrix_det G hG).continuous continuous_const
  have hc : IsCompact (metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)}) :=
    (metricFrameSet_isCompact g hK).prod isCompact_singleton
  have hsub : metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ V := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    change (normalWaveMetric g q 0).det ≠ 0
    rw [normalWaveMetric_zero g hq]
    simp
  have hF : ContDiffOn ℝ ∞ (fun q => ((G q)⁻¹,(G q).det⁻¹)) V := by
    apply ContDiffOn.prodMk
    · apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro j
      exact contDiffOn_matrix_inv G hG i j
    · exact (contDiff_matrix_det G hG).contDiffOn.inv (fun _ h => h)
  obtain ⟨ψ,hψ,he⟩ := smooth_extension_near_compact hc hV hsub hF
  obtain ⟨O,hO,hKO,hEq⟩ := mem_nhdsSet_iff_exists.mp he
  refine ⟨fun q => (ψ q).1,fun q => (ψ q).2,hψ.fst,hψ.snd,O,hO,hKO,?_⟩
  intro q hq
  have hh := hEq hq
  exact ⟨(congrArg Prod.fst hh).symm,(congrArg Prod.snd hh).symm⟩

def normalWaveFirstCoefficient (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : NormalWaveSpace) (j : Fin 3) : ℝ :=
  ∑ i, (fderiv ℝ (fun y => (normalWaveMetric g q y)⁻¹ i j) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) +
    (1/2 : ℝ) * (normalWaveMetric g q x)⁻¹ i j * (normalWaveMetric g q x).det⁻¹ *
      fderiv ℝ (fun y => (normalWaveMetric g q y).det) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))

lemma normalWaveMetric_det_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) : HasFDerivAt (𝕜 := ℝ)
      (fun x => (normalWaveMetric g q x).det) 0 0 := by
  have hd := (contDiff_matrix_det (id : Matrix (Fin 3) (Fin 3) ℝ → _) (fun _ _ => by fun_prop)).differentiable (by simp)
  have h := (hd (normalWaveMetric g q 0)).hasFDerivAt.comp 0
    (normalWaveMetric_first_jet g q)
  erw [ContinuousLinearMap.comp_zero] at h
  exact h

lemma normalWaveFirstCoefficient_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    normalWaveFirstCoefficient g q 0 = 0 := by
  let : ContinuousSMul ℝ NormalWaveSpace := IsBoundedSMul.continuousSMul
  funext j
  have hi := normalWaveInverse_first_jet g hq
  have hc (i j : Fin 3) : fderiv ℝ (fun y => (normalWaveMetric g q y)⁻¹ i j) 0 = 0 := by
    have h1 := (ContinuousLinearMap.proj i : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ)).hasFDerivAt.comp 0 hi
    have h2 := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp 0 h1
    have h := h2.fderiv
    erw [ContinuousLinearMap.comp_zero] at h
    exact h
  simp [normalWaveFirstCoefficient,hc,(normalWaveMetric_det_first_jet g q).fderiv]

theorem exists_normal_wave_coefficients (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ,
      ∃ b : NormalWaveParameter × NormalWaveSpace → Fin 3 → ℝ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      ∃ r > 0, ∀ q ∈ metricFrameSet g K,
        A (q,0) = 1 ∧ HasFDerivAt (𝕜 := ℝ) (fun x => A (q,x)) 0 0 ∧ b (q,0) = 0 ∧
        ∀ x ∈ Metric.ball (0 : NormalWaveSpace) r,
          A (q,x) = (normalWaveMetric g q x)⁻¹ ∧ b (q,x) = normalWaveFirstCoefficient g q x := by
  obtain ⟨A,d,hA,hd,O,hO,hsub,he⟩ := exists_normal_inverse_extension g hK
  let b := fun q : NormalWaveParameter × NormalWaveSpace => fun j : Fin 3 =>
    ∑ i, (fderiv ℝ (fun x => A (q.1,x) i j) q.2 (EuclideanSpace.basisFun (Fin 3) ℝ i) +
      (1/2 : ℝ) * A q i j * d q * fderiv ℝ (fun x => (normalWaveMetric g q.1 x).det) q.2
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hb : ContDiff ℝ ∞ b := by
    apply contDiff_pi.mpr
    intro j
    dsimp only [b]
    apply ContDiff.sum
    intro i _
    apply ContDiff.add
    · exact contDiff_parameter_fderiv_apply (fun q => A q i j) (contDiff_pi.mp (contDiff_pi.mp hA i) j) _
    · exact ((contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp hA i) j)).mul hd).mul
        (contDiff_parameter_fderiv_apply _
          (contDiff_matrix_det _ (contDiff_normalWaveMetric g)) _)
  have hgerm (q : NormalWaveParameter) (x : NormalWaveSpace) (hx : (q,x) ∈ O) :
      (fun y => A (q,y)) =ᶠ[𝓝 x] (fun y => (normalWaveMetric g q y)⁻¹) := by
    have ht : Tendsto (fun y : NormalWaveSpace => (q,y)) (𝓝 x) (𝓝 (q,x)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [ht (hO.mem_nhds hx)] with y hy
    exact (he (q,y) hy).1
  have hbe (q : NormalWaveParameter) (x : NormalWaveSpace) (hx : (q,x) ∈ O) :
      b (q,x) = normalWaveFirstCoefficient g q x := by
    funext j
    dsimp only [b,normalWaveFirstCoefficient]
    apply Finset.sum_congr rfl
    intro i _
    have hg : (fun y => A (q,y) i j) =ᶠ[𝓝 x] (fun y => (normalWaveMetric g q y)⁻¹ i j) :=
      (hgerm q x hx).fun_comp (fun M => M i j)
    rw [hg.fderiv_eq,(he (q,x) hx).1,(he (q,x) hx).2]
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hO hsub
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨A,b,hA,hb,r,hr,?_⟩
  intro q hq
  have hq0 : (q,0) ∈ O := hsub ⟨hq,mem_singleton 0⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [(he (q,0) hq0).1,normalWaveMetric_zero g hq]; simp
  · exact (normalWaveInverse_first_jet g hq).congr_of_eventuallyEq (hgerm q 0 hq0)
  · rw [hbe q 0 hq0,normalWaveFirstCoefficient_zero g hq]
  · intro x hx
    have hqx : (q,x) ∈ O := hUV ⟨hKU hq,hrV hx⟩
    exact ⟨(he (q,x) hqx).1,hbe q x hqx⟩


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
section Density
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma density_first_derivative {d a : E → ℝ} {x : E}
    (hd : DifferentiableAt ℝ d x) (ha : DifferentiableAt ℝ a x)
    (hx : 0 < d x) (v : E) :
    (Real.sqrt (d x))⁻¹ * fderiv ℝ (fun y => Real.sqrt (d y) * a y) x v =
      fderiv ℝ a x v + (1/2 : ℝ) * a x * (d x)⁻¹ * fderiv ℝ d x v := by
  erw [fderiv_fun_mul (hd.sqrt hx.ne') ha, _root_.add_apply]
  simp only [_root_.smul_apply, smul_eq_mul, fderiv_sqrt hd hx.ne']
  have hs : Real.sqrt (d x) ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hs2 : Real.sqrt (d x) ^ 2 = d x := Real.sq_sqrt hx.le
  field_simp
  rw [hs2]
  ring
end Density

lemma normalWaveDensity_firstCoefficient (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {x : NormalWaveSpace}
    (hx : 0 < (normalWaveMetric g q x).det) (j : Fin 3) :
    (Real.sqrt (normalWaveMetric g q x).det)⁻¹ *
      ∑ i, fderiv ℝ (fun y => Real.sqrt (normalWaveMetric g q y).det *
        (normalWaveMetric g q y)⁻¹ i j) x (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      normalWaveFirstCoefficient g q x j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun y => normalWaveMetric g q y i j) :=
    (contDiff_normalMetricTensor_apply g q.1 q.2
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
  have hd := (contDiff_matrix_det _ hG).differentiable (by simp) x
  have hO : IsOpen {y : NormalWaveSpace | (normalWaveMetric g q y).det ≠ 0} :=
    isOpen_ne_fun (contDiff_matrix_det _ hG).continuous continuous_const
  have ha := (contDiffOn_matrix_inv (normalWaveMetric g q) hG i j x hx.ne').contDiffAt
    (hO.mem_nhds hx.ne')
  exact density_first_derivative hd (ha.differentiableAt (by simp)) hx _

lemma compact_family_positive_radius {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] {K : Set P} (hK : IsCompact K)
    (f : P × E → ℝ) (hf : Continuous f) (hpos : ∀ p ∈ K, 0 < f (p,0)) :
    ∃ r > 0, ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r, 0 < f (p,x) := by
  let O : Set (P × E) := {q | 0 < f q}
  have hO : IsOpen O := isOpen_lt continuous_const hf
  have hsub : K ×ˢ {(0 : E)} ⊆ O := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    change 0 < f (p,x)
    have hx0 : x = 0 := hx
    rw [hx0]
    exact hpos p hp
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK
    isCompact_singleton hO hsub
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  exact ⟨r,hr,fun p hp x hx => hUV ⟨hKU hp,hrV hx⟩⟩

lemma compact_normal_density_radius (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.ball (0 : NormalWaveSpace) r,
      0 < (normalWaveMetric g q x).det := by
  apply compact_family_positive_radius (metricFrameSet_isCompact g hK)
    (fun q : NormalWaveParameter × NormalWaveSpace => (normalWaveMetric g q.1 q.2).det)
    (contDiff_matrix_det _ (contDiff_normalWaveMetric g)).continuous
  intro q hq
  rw [normalWaveMetric_zero g hq]
  simp

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev normalWaveEquiv : (Fin 3 → ℝ) ≃L[ℝ] NormalWaveSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

lemma normalWaveEquiv_single (i : Fin 3) :
    normalWaveEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

theorem exists_normal_wave_pi_coefficients (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ,
      ∃ b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      ∃ r > 0, ∀ q ∈ metricFrameSet g K,
        (∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
        (∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
        b (q,0) = 0 ∧
        ∀ x, ‖normalWaveEquiv x‖ < r →
          (∀ i j, A (q,x) i j = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ)) ∧
          (∀ j, b (q,x) j = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ)) := by
  obtain ⟨A,b,hA,hb,r,hr,he⟩ := exists_normal_wave_coefficients g hK
  let Ap := fun q : NormalWaveParameter × (Fin 3 → ℝ) =>
    fun i j : Fin 3 => (A (q.1,normalWaveEquiv q.2) i j : ℂ)
  let bp := fun q : NormalWaveParameter × (Fin 3 → ℝ) =>
    fun j : Fin 3 => (b (q.1,normalWaveEquiv q.2) j : ℂ)
  have hT : ContDiff ℝ ∞ (fun q : NormalWaveParameter × (Fin 3 → ℝ) => (q.1,normalWaveEquiv q.2)) :=
    contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)
  have hAp : ContDiff ℝ ∞ Ap := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_pi.mp (contDiff_pi.mp hA i) j).comp hT)
  have hbp : ContDiff ℝ ∞ bp := by
    apply contDiff_pi.mpr
    intro j
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_pi.mp hb j).comp hT)
  refine ⟨Ap,bp,hAp,hbp,r,hr,?_⟩
  intro q hq
  obtain ⟨h0,hd,hb0,heq⟩ := he q hq
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    simp only [Ap,map_zero,h0,Matrix.one_apply]
    split_ifs <;> simp
  · intro i j
    let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ)))
    have hf := (L.hasFDerivAt.comp 0 hd).comp 0 normalWaveEquiv.hasFDerivAt
    have hf' : HasFDerivAt (fun x => Ap (q,x) i j)
        ((L.comp 0).comp normalWaveEquiv.toContinuousLinearMap) 0 := hf
    simpa only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp] using hf'.fderiv
  · ext j
    simp [bp,hb0]
  · intro x hx
    have h := heq (normalWaveEquiv x) (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
    exact ⟨fun i j => by dsimp [Ap]; rw [h.1],fun j => by dsimp [bp]; rw [h.2]⟩

lemma normal_profile_family_smooth (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun q : NormalWaveParameter × NormalWaveSpace =>
      φ (normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2)) :=
  hφ.comp (contDiff_normalJetFamily g)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

lemma contDiff_smoothFiniteWave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E → ℂ} {V : ℕ → E → ℂ} (hS : ContDiff ℝ ∞ S)
    (hV : ∀ j, ContDiff ℝ ∞ (V j)) (J : ℕ) (n : ℝ) :
    ContDiff ℝ ∞ (smoothFiniteWave S V J n) := by
  unfold smoothFiniteWave
  exact (contDiff_const.mul hS).cexp.mul
    (ContDiff.sum (fun j _ => contDiff_const.mul (hV j)))

lemma contDiff_canonicalCutoffWave
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (m D : ℕ) (n : ℝ) :
    ContDiff ℝ ∞ (canonicalCutoffWave A b s z Q ζ m D n) :=
  contDiff_smoothFiniteWave (contDiff_realPolyEval _)
    (fun _ => hζ.mul (contDiff_realPolyEval _)) _ _

def normalWavePiOperator (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
    (f ∘ normalWaveEquiv.symm) (normalWaveEquiv x)

lemma normalWavePiOperator_eq (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Fin 3 → ℝ) :
    normalWavePiOperator g q f x =
      waveCoordinateOperator (fun i => Pi.single i 1)
        (fun i j y => ((normalWaveMetric g q (normalWaveEquiv y))⁻¹ i j : ℂ))
        (fun j y => (normalWaveFirstCoefficient g q (normalWaveEquiv y) j : ℂ)) f x := by
  have h := waveCoordinateOperator_comp_linear normalWaveEquiv.toContinuousLinearMap
    (fun i => Pi.single i 1)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
    (hf.comp normalWaveEquiv.symm.contDiff) x
  simpa only [normalWavePiOperator,Function.comp_def,ContinuousLinearEquiv.coe_coe,
    normalWaveEquiv_single,ContinuousLinearEquiv.symm_apply_apply] using h.symm

lemma normalWavePiOperator_eq_extension (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (x : Fin 3 → ℝ)
    (hA : ∀ i j, A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
    (hb : ∀ j, b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ)) :
    normalWavePiOperator g q f x = waveCoordinateOperator (fun i => Pi.single i 1) A b f x := by
  rw [normalWavePiOperator_eq g q hf]
  simp only [waveCoordinateOperator,hA,hb]



end YauCounterexamples
end

end OAI
