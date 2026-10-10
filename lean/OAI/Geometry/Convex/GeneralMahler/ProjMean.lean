import OAI.Geometry.Convex.GeneralMahler.Matrix
import OAI.Geometry.Convex.GeneralMahler.Proj
import OAI.Geometry.Convex.GeneralMahler.IBP

namespace OAI

/-! Biased projection lemma §02: mean derivative -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} (C : ProperCone ℝ (Rn m))

/-- Projection Jacobian, zero at undefined points. -/
def projJac (x : (Rn m)) : Mat m := op.symm (fderiv ℝ (coneProj C) x)

@[simp] lemma projJac_op (x : (Rn m)) :
    op (projJac C x) = fderiv ℝ (coneProj C) x := by simp [projJac]

lemma projJac_sym (x : (Rn m)) : (projJac C x).IsHermitian :=
  op_iff_hermitian.mpr fun v w => by
    simp only [projJac_op]; exact coneProj_fderiv_symmetric C x v w
lemma projJac_pos (x : (Rn m)) : (projJac C x).PosSemidef :=
  op_posSemidef_iff.mpr ⟨projJac_sym C x,fun v => by
    simp only [projJac_op]; exact coneProj_fderiv_pos C x v⟩

lemma projJac_norm (x:(Rn m)) : ‖projJac C x‖ ≤ 1 := by
  rw [← op_norm,projJac_op]
  exact norm_fderiv_le_of_lipschitz ℝ (coneProj_lip C)

lemma projJac_le_one (x:(Rn m)) : projJac C x ≤ 1 :=
  le_one_norm _ (projJac_sym C x) (projJac_norm C x)

lemma projJac_id {x : (Rn m)} (hx : x ∈ interior (C:Set (Rn m))) :
    projJac C x = 1 := by
  have h : coneProj C =ᶠ[𝓝 x] id := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact proj_of_mem C hy
  rw [projJac,h.fderiv_eq,fderiv_id]
  change op.symm 1 = 1
  exact _root_.map_one _

lemma projJac_zero {x : (Rn m)} (hx : -x ∈ interior (posDual C:Set (Rn m))) :
    projJac C x = 0 := by
  have h : coneProj C =ᶠ[𝓝 x] (fun _ => 0) := by
    have ht : ∀ᶠ y in 𝓝 x, -y ∈ (posDual C:Set (Rn m)) :=
      (continuous_neg.tendsto x) (mem_interior_iff_mem_nhds.mp hx)
    exact ht.mono fun y hy => proj_zero_of_dual C y hy
  simp [projJac,h.fderiv_eq]

lemma strongly_projJac : StronglyMeasurable (projJac C) := by
  let g := fderiv ℝ (coneProj C)
  have he : projJac C = op.symm ∘ g := rfl
  have hm := (measurable_fderiv ℝ (coneProj C)).stronglyMeasurable
  rw [he]; exact continuous_op_symm.comp_stronglyMeasurable hm

variable (B : (Rn m) ≃L[ℝ] (Rn m))
def affineN (a g : (Rn m)) : (Rn m) := B g + a
@[fun_prop] lemma continuous_affineN (a : (Rn m)) : Continuous (affineN B a) := by
  unfold affineN; fun_prop

lemma tendsto_ae_affineN (a : (Rn m)) :
    Tendsto (affineN B a) (ae (normal m)) (ae volume) := by
  have he := (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae
  have hn : LinearMap.det (B : (Rn m) →ₗ[ℝ] (Rn m)) ≠ 0 := by

    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hy := LinearMap.quasiMeasurePreserving volume (B : (Rn m) →ₗ[ℝ] (Rn m)) hn
  exact (he.comp hy.tendsto_ae).mono_left normal_ac.ae_le

lemma affineN_integrable (a : (Rn m)) : Integrable (affineN B a) (normal m) :=
  (((PolyBound.clm B.toContinuousLinearMap).add (PolyBound.const a))).gaussian_integrable
    (continuous_affineN B a).aestronglyMeasurable

lemma affineN_mean (a:(Rn m)) : ∫ x, affineN B a x ∂normal m = a := by
  change ∫ x, B x + a ∂normal m = _
  have hi : Integrable id (normal m) := ProbabilityTheory.IsGaussian.integrable_id
  let b := B.toContinuousLinearMap
  have hb : Integrable (fun x => b x) (normal m) := b.integrable_comp hi
  change ∫ x, b x + a ∂normal m = a
  rw [integral_add hb (integrable_const _)]
  have he : (∫ x, b x ∂normal m) = 0 := by
    rw [show (∫ x, b x ∂normal m) = _ from b.integral_comp_comm (φ := id) hi]
    simp [normal]
  change (∫ x, b x ∂normal m) + _ = _
  simp [he]

def sample (a x : (Rn m)) := coneProj C (affineN B a x)

lemma continuous_sample (a:(Rn m)) : Continuous (sample C B a) :=
  (coneProj_lip C).continuous.comp (continuous_affineN B a)

lemma poly_sample (a : (Rn m)) : PolyBound (sample C B a) :=
  (PolyBound.lipschitz (coneProj_lip C)).comp
    ((PolyBound.clm B.toContinuousLinearMap).add (PolyBound.const a))

lemma sample_integrable (a : (Rn m)) : Integrable (sample C B a) (normal m) :=
  (poly_sample ..).gaussian_integrable (continuous_sample ..).aestronglyMeasurable

def mean (a : (Rn m)) : (Rn m) := ∫ x, sample C B a x ∂normal m
def meanJac (a : (Rn m)) : Mat m := ∫ x, projJac C (affineN B a x) ∂normal m

lemma meanJac_integrable (a : (Rn m)) :
    Integrable (fun x => projJac C (affineN B a x)) (normal m) := by
  have hm := (strongly_projJac C).comp_measurable (continuous_affineN B a).measurable
  apply PolyBound.gaussian_integrable _ hm.aestronglyMeasurable
  exact PolyBound.of_bound 1 (fun x => projJac_norm C _)

theorem hasFDerivAt_mean (a : (Rn m)) :
    HasFDerivAt (mean C B) (op (meanJac C B a)) a := by
  let : CompleteSpace (Rn m →L[ℝ] Rn m) := ContinuousLinearMap.instCompleteSpace
  let d := fun x => fderiv ℝ (coneProj C) (affineN B a x)
  have he : op (meanJac C B a) = ∫ x, d x ∂normal m := by
    have h := opCLE.toContinuousLinearMap.integral_comp_comm (meanJac_integrable C B a)
    symm
    change (∫ x, d x ∂_) = op _
    simpa only [ContinuousLinearEquiv.coe_coe, meanJac, opCLE_apply,projJac_op] using h
  rw [he]
  have hl : ∀ᵐ g ∂normal m, ∀ y ∈ Set.univ,
      ‖sample C B y g - sample C B a g‖ ≤ 1 * ‖y-a‖ := by
    apply ae_of_all; intro g y _
    simpa only [sample, affineN,NNReal.coe_one, ← dist_eq_norm, dist_add_left] using
      (coneProj_lip C).dist_le_mul (B g + y) (B g + a)
  have hm : AEStronglyMeasurable d (normal m) :=
    ((measurable_fderiv ..).comp (continuous_affineN B a).measurable).aestronglyMeasurable
  have hd := hasFDerivAt_integral_of_dominated_loc_of_lip' univ_mem
    (fun y _ => (continuous_sample C B y).aestronglyMeasurable)
    (sample_integrable C B a) hm hl (integrable_const _) (show
    ∀ᵐ g ∂normal m, HasFDerivAt (fun y => sample C B y g) (d g) a from ?_)
  exact hd.2
  have hh := (coneProj_lip C).ae_differentiableAt (μ := volume)
  filter_upwards [(tendsto_ae_affineN B a).eventually hh] with g hg
  have ha := hg.hasFDerivAt
  simpa only [sample,affineN,d,Function.comp_def,zero_add,ContinuousLinearMap.comp_id] using
    ha.comp a ((hasFDerivAt_const (B g) a).add (hasFDerivAt_id a))

theorem mean_C_one : ContDiff ℝ 1 (mean C B) := by
  let F := coneProj C ∘ B
  have hc : Continuous F := (coneProj_lip C).continuous.comp B.continuous
  have hp : PolyBound F :=
    (PolyBound.lipschitz (coneProj_lip C)).comp (PolyBound.clm B.toContinuousLinearMap)
  have hd := smoothG_hasFDeriv hp hc.stronglyMeasurable
  have hsf : ContDiff ℝ 1 (smoothG F) := by
    refine contDiff_one_iff_fderiv.mpr ⟨fun x => (hd x).2.differentiableAt,?_⟩
    have he := funext fun x => (hd x).2.fderiv
    rw [he]
    exact smoothG_deriv_cont hp hc.stronglyMeasurable
  have he : mean C B = smoothG F ∘ B.symm := by
    ext a

    simp only [mean,smoothG,F,sample,affineN,Function.comp_def,map_add,B.apply_symm_apply]
  rw [he]; exact hsf.comp B.symm.contDiff

-- strict inequalities for the average derivative
lemma prob_open (a : (Rn m)) (s : Set (Rn m)) (hs : IsOpen s) (he : s.Nonempty) :
    0 < normal m ((affineN B a) ⁻¹' s) := by
  let : (normal m).IsOpenPosMeasure := ac_normal.isOpenPosMeasure
  apply (hs.preimage (continuous_affineN B a)).measure_pos (normal m)
  rcases he with ⟨x,hx⟩
  use B.symm (x-a)
  simpa [affineN]

lemma strict_pos_of_layer {μ : Measure (Rn m)} {A : (Rn m) → Mat m} (hi : Integrable A μ)
    (hh : ∀ x, (A x).PosSemidef) {s : Set (Rn m)} (hp : 0 < μ s)
    (he : ∀ x ∈ s, A x = 1) :
    (∫ x, A x ∂μ).PosDef := by
  apply op_posDef_iff.mpr
  refine ⟨(psd_integral hi (ae_of_all _ hh)).1, fun v hv => ?_⟩
  rw [op_inner_integral hi]
  refine (integral_pos_iff_support_of_nonneg (fun x => (op_posSemidef_iff.mp (hh x)).2 v)
    (integral_opPair hi _ _)).mpr (lt_of_lt_of_le hp (measure_mono ?_))
  intro x hx
  have hh : 0 < ⟪v, op (A x) v⟫ := by
    rw [he x hx, _root_.map_one]; exact real_inner_self_pos.mpr hv
  exact hh.ne'

theorem mean_pos (hc : (interior (C : Set (Rn m))).Nonempty) (x : (Rn m)) :
    (meanJac C B x).PosDef :=
  strict_pos_of_layer (meanJac_integrable ..) (fun _ => projJac_pos ..)
    (prob_open B x _ isOpen_interior hc) (fun _ hx => projJac_id C hx)

theorem mean_lt_one (hd : (interior (posDual C : Set (Rn m))).Nonempty) (x : (Rn m)) :
    ((1 : Mat m)-meanJac C B x).PosDef := by
  let A := fun y => (1:Mat m) - projJac C (affineN B x y)
  have hi := meanJac_integrable C B x
  have hx : 1 - meanJac C B x = ∫ y, A y ∂normal m := by
    rw [meanJac,show (∫ y, A y ∂normal m)=_ from integral_sub (integrable_const _) hi]
    simp
  rw [hx]
  let s := (fun y : (Rn m) => -y) ⁻¹' interior (posDual C : Set (Rn m))
  have hp := prob_open B x s (isOpen_interior.preimage continuous_neg) (by
    rcases hd with ⟨y,hy⟩; exact ⟨-y,by simpa [s]⟩)
  apply strict_pos_of_layer ((integrable_const _).sub hi) _ hp _
  · intro y; exact Matrix.le_iff.mp (projJac_le_one ..)
  · intro y hy
    change (1:Mat m)-projJac C (affineN B x y) = _
    rw [projJac_zero C hy,sub_zero]
end GeneralMahler

end

end OAI
