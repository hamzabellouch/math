import OAI.Analysis.StrictMeans.InfinityEscape

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma compact_integral_deriv_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) : ∫ x, deriv g x = 0 := by
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hg.differentiable one_ne_zero x).hasDerivAt)
    ((hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv)
    (hg.continuous.integrable_of_hasCompactSupport hc)

lemma compact_second_deriv_green {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ t in Ioi s, (t - s) * deriv (deriv g) t) = g s := by
  let H : ℝ → ℝ := fun t => (t - s) * deriv g t - g t
  have h1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hH : ContDiff ℝ 1 H :=
    ((contDiff_id.sub contDiff_const).mul h1).sub (hg.of_le (by norm_num))
  have hcH : HasCompactSupport H := (hc.deriv.mul_left).sub hc
  have hder (t : ℝ) : deriv H t = (t - s) * deriv (deriv g) t := by
    have h := (((hasDerivAt_id t).sub_const s).mul
      ((h1.differentiable one_ne_zero t).hasDerivAt)).sub
      ((hg.differentiable (by norm_num) t).hasDerivAt)
    have he : ((fun x => id x - s) * deriv g - g) = H := rfl
    rw [he] at h
    rw [h.deriv]
    simp
  simpa only [H, hder, sub_self, zero_mul, zero_sub, neg_neg] using
    hcH.integral_Ioi_deriv_eq hH s

def realPlanePartial (v : ℝ × ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ g p v

lemma contDiff_realPlanePartial {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (realPlanePartial v g) := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma compact_realPlanePartial {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (v : ℝ × ℝ) :
    HasCompactSupport (realPlanePartial v g) := hc.fderiv_apply ℝ v

lemma deriv_vertical_line {g : ℝ × ℝ → ℝ} {x y : ℝ} (hg : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t => g (x,t)) y = realPlanePartial (0,1) g (x,y) := by
  exact (hg.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

lemma deriv_horizontal_line {g : ℝ × ℝ → ℝ} {x y : ℝ} (hg : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t => g (t,y)) x = realPlanePartial (1,0) g (x,y) := by
  exact (hg.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

lemma compact_vertical_line {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (x : ℝ) :
    HasCompactSupport (fun y => g (x,y)) := by
  apply hc.comp_isClosedEmbedding
  exact ⟨isEmbedding_prodMkRight x, (isClosedMap_prodMk_left x).isClosed_range⟩

lemma compact_horizontal_line {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (y : ℝ) :
    HasCompactSupport (fun x => g (x,y)) := by
  apply hc.comp_isClosedEmbedding
  exact ⟨isEmbedding_prodMkLeft y, (isClosedMap_prodMk_right y).isClosed_range⟩

lemma compact_plane_second_horizontal_zero {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
  (hc : HasCompactSupport g) (y : ℝ) :
  (∫ x, realPlanePartial (1,0) (realPlanePartial (1,0) g) (x,y)) = 0 := by
  have hdx := contDiff_realPlanePartial hg (1,0)
  have hL : ContDiff ℝ 2 (fun x => g (x,y)) :=
    contDiff_infty.mp (hg.comp (contDiff_id.prodMk contDiff_const)) 2
  have hL' : deriv (fun x => g (x,y)) = fun x => realPlanePartial (1,0) g (x,y) := by
    funext x
    exact deriv_horizontal_line (hg.differentiable (by simp) (x,y))
  have hL'' : deriv (deriv (fun x => g (x,y))) = fun x => realPlanePartial (1,0) (realPlanePartial (1,0) g) (x,y) := by
    rw [hL']
    funext x
    exact deriv_horizontal_line (hdx.differentiable (by simp) (x,y))
  simpa only [hL''] using compact_integral_deriv_zero hL.deriv'
    (compact_horizontal_line hc y).deriv

lemma compact_plane_second_vertical_green {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
  (hc : HasCompactSupport g) (x s : ℝ) :
  (∫ y in Ioi s, (y - s) * realPlanePartial (0,1) (realPlanePartial (0,1) g) (x,y)) = g (x,s) := by
  have hdy := contDiff_realPlanePartial hg (0,1)
  have hL : ContDiff ℝ 2 (fun y => g (x,y)) :=
    contDiff_infty.mp (hg.comp (contDiff_const.prodMk contDiff_id)) 2
  have hL' : deriv (fun y => g (x,y)) = fun y => realPlanePartial (0,1) g (x,y) := by
    funext y
    exact deriv_vertical_line (hg.differentiable (by simp) (x,y))
  have hL'' : deriv (deriv (fun y => g (x,y))) = fun y => realPlanePartial (0,1) (realPlanePartial (0,1) g) (x,y) := by
    rw [hL']
    funext y
    exact deriv_vertical_line (hdy.differentiable (by simp) (x,y))
  simpa only [hL''] using compact_second_deriv_green hL (compact_vertical_line hc x) s

lemma compact_plane_weight_integrable {D : ℝ × ℝ → ℝ} (hD : Continuous D)
    (hc : HasCompactSupport D) (s : ℝ) :
    Integrable (fun p : ℝ × ℝ => (p.2 - s) * D p)
      (volume.prod (volume.restrict (Ioi s))) :=
  ((continuous_snd.sub continuous_const).mul hD).integrable_of_hasCompactSupport hc.mul_left

lemma compact_plane_horizontal_integral_zero {X : ℝ × ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hcX : HasCompactSupport X)
    (hxx : ∀ y : ℝ, (∫ x, X (x,y)) = 0) :
    (∫ p : ℝ × ℝ, (p.2-s) * X p ∂(volume.prod (volume.restrict (Ioi s)))) = 0 := by
  have hi := compact_plane_weight_integrable hX hcX s
  rw [integral_prod _ hi]
  have he : (∫ x : ℝ, ∫ y in Ioi s, (y-s)*X (x,y)) =
      ∫ y in Ioi s, ∫ x : ℝ, (y-s)*X (x,y) :=
    integral_integral_swap_of_hasCompactSupport
      ((continuous_snd.sub continuous_const).mul hX) hcX.mul_left
  rw [he]
  simp only [integral_const_mul, hxx, mul_zero, integral_zero]

lemma compact_plane_green_assemble {X Y : ℝ × ℝ → ℝ} {H : ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hcX : HasCompactSupport X)
    (hY : Continuous Y) (hcY : HasCompactSupport Y)
    (hxx : ∀ y : ℝ, (∫ x, X (x,y)) = 0)
    (hyy : ∀ x : ℝ, (∫ y in Ioi s, (y - s) * Y (x,y)) = H x) :
    (∫ x, H x) = ∫ p : ℝ × ℝ, (p.2 - s) * (X p + Y p)
      ∂(volume.prod (volume.restrict (Ioi s))) := by
  have hiX := compact_plane_weight_integrable hX hcX s
  have hiY := compact_plane_weight_integrable hY hcY s
  have he : (fun p : ℝ × ℝ => (p.2-s)*(X p+Y p)) =
      (fun p => (p.2-s)*X p + (p.2-s)*Y p) := by
    funext p
    exact mul_add _ _ _
  rw [he, integral_add hiX hiY, compact_plane_horizontal_integral_zero hX hcX hxx,
    zero_add, integral_prod _ hiY]
  simp only [hyy]

lemma compact_plane_horizontal_green {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ x, g (x,s)) =
    ∫ p : ℝ × ℝ, (p.2 - s) *
      (realPlanePartial (1,0) (realPlanePartial (1,0) g) p +
       realPlanePartial (0,1) (realPlanePartial (0,1) g) p)
      ∂(volume.prod (volume.restrict (Ioi s))) := by
  apply compact_plane_green_assemble
  · exact (contDiff_realPlanePartial (contDiff_realPlanePartial hg (1,0)) (1,0)).continuous
  · exact (compact_realPlanePartial (compact_realPlanePartial hc (1,0)) (1,0))
  · exact (contDiff_realPlanePartial (contDiff_realPlanePartial hg (0,1)) (0,1)).continuous
  · exact (compact_realPlanePartial (compact_realPlanePartial hc (0,1)) (0,1))
  · exact compact_plane_second_horizontal_zero hg hc
  · exact fun x => compact_plane_second_vertical_green hg hc x s

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def planePartial (v : ℂ) (g : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ g z v

def planeLaplacian (g : ℂ → ℝ) (z : ℂ) : ℝ :=
  planePartial 1 (planePartial 1 g) z + planePartial I (planePartial I g) z

lemma planePartial_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hψ : DifferentiableAt ℝ ψ (F z)) (v : ℂ) :
    planePartial v (fun w => ψ (F w)) z = fderiv ℝ ψ (F z) (deriv F z * v) := by
  change (fderiv ℝ (ψ ∘ F) z) v = _
  rw [fderiv_comp z hψ (hF.restrictScalars (𝕜 := ℝ))]
  simp only [ContinuousLinearMap.comp_apply, hF.hasDerivAt.complexToReal_fderiv.fderiv]
  rfl

lemma second_planePartial_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hψ : ContDiffAt ℝ 2 ψ (F z)) (v : ℂ) :
    planePartial v (planePartial v (fun w => ψ (F w))) z =
      fderiv ℝ ψ (F z) (deriv (deriv F) z * v * v) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * v) (deriv F z * v) := by
  have he : planePartial v (fun w => ψ (F w)) =ᶠ[𝓝 z]
      fun w => fderiv ℝ ψ (F w) (deriv F w * v) := by
    have hp := hψ.eventually (by norm_num)
    filter_upwards [hF.eventually_analyticAt, hF.continuousAt.eventually hp] with w hw hpw
    exact planePartial_comp_holomorphic hw.differentiableAt
      (hpw.differentiableAt (by norm_num)) v
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) (F z) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA := hDψ.hasFDerivAt.comp z hF.differentiableAt.hasDerivAt.complexToReal_fderiv
  have hB := ((hF.deriv.differentiableAt.hasDerivAt).mul_const v).complexToReal_fderiv
  change fderiv ℝ (planePartial v (fun w => ψ (F w))) z v = _
  rw [he.fderiv_eq]
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hA.clm_apply hB).fderiv
  simpa only [Function.comp_def, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, smul_apply, one_apply_eq_self,
    smul_eq_mul] using hh

lemma real_bilinear_complex_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (a * I) (a * I) = ‖a‖ ^ 2 * (B 1 1 + B I I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • I := by apply Complex.ext <;> simp
  have hai : a * I = (-a.im) • (1 : ℂ) + a.re • I := by apply Complex.ext <;> simp
  calc
    B a a + B (a * I) (a * I) =
        B (a.re • 1 + a.im • I) (a.re • 1 + a.im • I) +
        B ((-a.im) • 1 + a.re • I) ((-a.im) • 1 + a.re • I) := by rw [← ha, ← hai]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

lemma planeLaplacian_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hψ : ContDiffAt ℝ 2 ψ (F z)) :
    planeLaplacian (fun w => ψ (F w)) z = ‖deriv F z‖ ^ 2 * planeLaplacian ψ (F z) := by
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) (F z) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp (v : ℂ) : planePartial v (planePartial v ψ) (F z) =
      fderiv ℝ (fderiv ℝ ψ) (F z) v v := by
    unfold planePartial
    rw [fderiv_clm_apply hDψ (differentiableAt_const v)]
    simp
  rw [planeLaplacian, second_planePartial_comp_holomorphic hF hψ,
    second_planePartial_comp_holomorphic hF hψ]
  simp only [mul_one, mul_assoc, I_mul_I, mul_neg_one, map_neg]
  rw [show fderiv ℝ ψ (F z) (deriv (deriv F) z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z) (deriv F z) +
      (-fderiv ℝ ψ (F z) (deriv (deriv F) z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * I) (deriv F z * I)) =
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z) (deriv F z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * I) (deriv F z * I) by ring]
  rw [real_bilinear_complex_trace]
  simp only [planeLaplacian, hp]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma planePartial_contDiff {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (v : ℂ) :
    ContDiff ℝ ∞ (planePartial v g) := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma partial_realProd_comp {g : ℂ → ℝ} (hg : Differentiable ℝ g) (v : ℝ × ℝ) :
    realPlanePartial v (fun p => g (Complex.equivRealProdCLM.symm p)) =
      fun p => planePartial (Complex.equivRealProdCLM.symm v) g (Complex.equivRealProdCLM.symm p) := by
  funext p
  unfold realPlanePartial planePartial
  change fderiv ℝ (g ∘ Complex.equivRealProdCLM.symm) p v = _
  rw [fderiv_comp p (hg _) Complex.equivRealProdCLM.symm.differentiableAt,
    Complex.equivRealProdCLM.symm.fderiv]
  rfl

lemma laplacian_realProd_comp {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    realPlanePartial (1,0) (realPlanePartial (1,0)
      (fun p => g (Complex.equivRealProdCLM.symm p))) p +
    realPlanePartial (0,1) (realPlanePartial (0,1)
      (fun p => g (Complex.equivRealProdCLM.symm p))) p =
      planeLaplacian g (Complex.equivRealProdCLM.symm p) := by
  rw [partial_realProd_comp (hg.differentiable (by simp)),
    partial_realProd_comp ((planePartial_contDiff hg _).differentiable (by simp)),
    partial_realProd_comp (hg.differentiable (by simp)),
    partial_realProd_comp ((planePartial_contDiff hg _).differentiable (by simp))]
  rfl

lemma integral_realProd_above (H : ℂ → ℝ) (s : ℝ) :
    (∫ p : ℝ × ℝ, H (Complex.equivRealProdCLM.symm p)
      ∂(volume.prod (volume.restrict (Ioi s)))) =
    ∫ z in {z : ℂ | s < z.im}, H z := by
  have hp := Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (MeasurableSet.univ.prod measurableSet_Ioi : MeasurableSet ((univ : Set ℝ) ×ˢ Ioi s))
  have he := hp.integral_comp Complex.measurableEquivRealProd.measurableEmbedding
    (fun p => H (Complex.equivRealProdCLM.symm p))
  have hm : (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Ioi s) =
      volume.prod (volume.restrict (Ioi s)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm] at he
  have hs : (Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ Ioi s)) =
      {z : ℂ | s < z.im} := by ext z; simp
  have hx (z : ℂ) : Complex.equivRealProdCLM.symm (Complex.measurableEquivRealProd z) = z :=
    Complex.equivRealProdCLM.symm_apply_apply z
  simpa only [hs, hx] using he.symm

lemma compact_complex_horizontal_green {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ x : ℝ, g ((x : ℂ) + (s : ℂ) * I)) =
    ∫ z in {z : ℂ | s < z.im}, (z.im-s) * planeLaplacian g z := by
  have hgc : ContDiff ℝ ∞ (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hg.comp Complex.equivRealProdCLM.symm.contDiff
  have hcc : HasCompactSupport (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hc.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding
  have he := compact_plane_horizontal_green hgc hcc s
  simp only [laplacian_realProd_comp hg] at he
  have hz (x : ℝ) : Complex.equivRealProdCLM.symm (x,s) = (x : ℂ) + (s : ℂ) * I := by
    apply Complex.ext <;> simp
  simp only [hz] at he
  rw [he]
  exact integral_realProd_above (fun z => (z.im-s) * planeLaplacian g z) s

lemma planeLaplacian_congr_nhds {g h : ℂ → ℝ} {z : ℂ} (he : g =ᶠ[𝓝 z] h) :
    planeLaplacian g z = planeLaplacian h z := by
  have hp (v : ℂ) : planePartial v g =ᶠ[𝓝 z] planePartial v h := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hw
  change fderiv ℝ (planePartial 1 g) z 1 + fderiv ℝ (planePartial I g) z I =
    fderiv ℝ (planePartial 1 h) z 1 + fderiv ℝ (planePartial I h) z I
  rw [(hp 1).fderiv_eq, (hp I).fderiv_eq]

end
end StrictInverseFirstPower

end

end OAI
