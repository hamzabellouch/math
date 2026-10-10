import OAI.Analysis.HotSpots.VectorEnergy

namespace OAI

section LipschitzMollifier

noncomputable section
open Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff InnerProductSpace ENNReal NNReal Convolution
namespace StrictHotSpots


def ambientSmooth (φ : ContDiffBump (0 : Plane)) (b : Plane → ℝ) : Plane → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ,volume] b

lemma ambientSmooth_smooth (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) : ContDiff ℝ ∞ (ambientSmooth φ b) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hb.continuous.locallyIntegrable

lemma ambientSmooth_integrable (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    Integrable (fun t : Plane => φ.normed volume t * b (x-t)) :=
  φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) φ.integrable_normed.locallyIntegrable hb.continuous x

lemma ambientSmooth_lipschitz (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) : LipschitzWith L (ambientSmooth φ b) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have hi := (ambientSmooth_integrable φ hb x).sub (ambientSmooth_integrable φ hb y)
  have hp (t : Plane) : ‖φ.normed volume t*b (x-t)-φ.normed volume t*b (y-t)‖ ≤
      φ.normed volume t*((L:ℝ)*‖x-y‖) := by
    rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed t)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
    simpa only [sub_sub_sub_cancel_right] using hb.norm_sub_le (x-t) (y-t)
  change ‖(∫ t : Plane, φ.normed volume t*b (x-t))-(∫ t : Plane, φ.normed volume t*b (y-t))‖ ≤ _
  rw [← integral_sub (ambientSmooth_integrable φ hb x) (ambientSmooth_integrable φ hb y)]
  calc
    _ ≤ ∫ t : Plane, ‖φ.normed volume t*b (x-t)-φ.normed volume t*b (y-t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Plane, φ.normed volume t*((L:ℝ)*‖x-y‖) :=
      integral_mono hi.norm (φ.integrable_normed.mul_const _) hp
    _ = _ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma ambientSmooth_tendsto {φ : ℕ → ContDiffBump (0 : Plane)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (nhds 0)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    Tendsto (fun n => ambientSmooth (φ n) b x) atTop (nhds (b x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous hφ hb.continuous x

lemma ambientSmooth_fderiv (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    fderiv ℝ (ambientSmooth φ b) x = ∫ t : Plane, φ.normed volume t • fderiv ℝ b (x-t) := by
  have hm : AEStronglyMeasurable (fun t : Plane => φ.normed volume t • fderiv ℝ b (x-t)) volume :=
    (φ.continuous_normed.measurable.smul ((measurable_fderiv ℝ b).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hl : ∀ᵐ t : Plane ∂volume, LipschitzOnWith
      (Real.nnabs (φ.normed volume t*(L:ℝ))) (fun y => φ.normed volume t*b (y-t)) univ := by
    filter_upwards [] with t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [dist_eq_norm,← mul_sub,norm_mul,Real.norm_eq_abs,Real.coe_nnabs,
      abs_of_nonneg (mul_nonneg (φ.nonneg_normed t) L.coe_nonneg),
      abs_of_nonneg (φ.nonneg_normed t)]
    calc
      _ ≤ φ.normed volume t*((L:ℝ)*‖(y-t)-(z-t)‖) :=
        mul_le_mul_of_nonneg_left (hb.norm_sub_le _ _) (φ.nonneg_normed t)
      _ = _ := by rw [sub_sub_sub_cancel_right]; ring
  have hd : ∀ᵐ t : Plane ∂volume, HasFDerivAt (fun y => φ.normed volume t*b (y-t))
      (φ.normed volume t • fderiv ℝ b (x-t)) x := by
    filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (hb.ae_differentiableAt (μ := volume))] with t ht
    have h := ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
    simpa [Function.comp_def,Pi.smul_def,smul_eq_mul] using h.const_smul (φ.normed volume t)
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip (s := univ)
    (bound := fun t => φ.normed volume t*(L:ℝ)) (by simp : univ ∈ nhds x)
    (Filter.Eventually.of_forall (fun y => (ambientSmooth_integrable φ hb y).aestronglyMeasurable))
    (ambientSmooth_integrable φ hb x) hm hl (φ.integrable_normed.mul_const _) hd
  exact hh.2.fderiv

lemma ambientSmooth_gradient (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    gradient (ambientSmooth φ b) x =
      (φ.normed volume ⋆[lsmul ℝ ℝ,volume] gradient b) x := by
  unfold gradient
  rw [ambientSmooth_fderiv φ hb x]
  apply ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.integral_comp_comm
    (fun t : Plane => φ.normed volume t • fderiv ℝ b (x-t))).symm.trans
  apply integral_congr_ae
  filter_upwards [] with t
  exact map_smul _ _ _

lemma lipschitz_gradient_locallyIntegrable {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    LocallyIntegrable (gradient b) volume := by
  have hm : Measurable (gradient b) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ b)
  apply (memLp_top_of_bound hm.aestronglyMeasurable (L:ℝ) ?_).locallyIntegrable (by simp)
  filter_upwards [] with x
  change ‖(InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ b x)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hb

lemma ambientSmooth_gradient_tendsto {φ : ℕ → ContDiffBump (0 : Plane)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (nhds 0)) {K : ℝ}
    (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K*(φ n).rIn) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) :
    ∀ᵐ x : Plane ∂volume, Tendsto (fun n => gradient (ambientSmooth (φ n) b) x) atTop (nhds (gradient b x)) := by
  simp_rw [ambientSmooth_gradient _ hb]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hK
    (lipschitz_gradient_locallyIntegrable hb)

end StrictHotSpots
end
end LipschitzMollifier

section LipschitzH1

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots


lemma HasH1Gradient.of_tendsto_L2 {Ω : Set Plane} {f : ℕ → Plane → ℝ} {g : ℕ → Plane → Plane}
    (hf : ∀ n, HasH1Gradient Ω (f n) (g n)) {u : Plane → ℝ} {v : Plane → Plane}
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hfu : Tendsto (fun n => (hf n).1.toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hgv : Tendsto (fun n => (hf n).2.1.toLp (g n)) atTop (𝓝 (hv.toLp v))) :
    HasH1Gradient Ω u v := by
  have ht : Tendsto (fun n => (hf n).toH1.val) atTop
      (𝓝 (WithLp.toLp 2 (hu.toLp u,hv.toLp v))) :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hfu.prodMk_nhds hgv)
  have hg := (h1Graph_mem_iff Ω (WithLp.toLp 2 (hu.toLp u,hv.toLp v))).mp
    ((h1Graph_closed Ω).mem_of_tendsto ht (Eventually.of_forall fun n => (hf n).toH1.property))
  exact hg.congr hu.coeFn_toLp hv.coeFn_toLp

def planeApproxBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := (2*((n:ℝ)+1))⁻¹
  rOut := ((n:ℝ)+1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply inv_strictAnti₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma planeApproxBump_rOut_tendsto :
    Tendsto (fun n => (planeApproxBump n).rOut) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma planeApproxBump_ratio (n : ℕ) :
    (planeApproxBump n).rOut ≤ 2*(planeApproxBump n).rIn := by
  dsimp only [planeApproxBump]
  have h : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  norm_num

lemma planeApproxBump_rOut_le_one (n : ℕ) : (planeApproxBump n).rOut ≤ 1 := by
  change ((n:ℝ)+1)⁻¹ ≤ 1
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma ambientSmooth_error (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    ‖ambientSmooth φ b x-b x‖ ≤ (L:ℝ)*φ.rOut := by
  rw [← dist_eq_norm]
  apply φ.dist_normed_convolution_le hb.continuous.aestronglyMeasurable
  intro y hy
  exact (hb.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg)

lemma lipschitz_gradient_bound {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    ‖gradient b x‖ ≤ L := by
  change ‖(InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ b x)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hb

lemma lipschitz_gradient_memLp_top {Ω : Set Plane} {b : Plane → ℝ} {L : ℝ≥0}
    (hb : LipschitzWith L b) : MemLp (gradient b) ∞ (volume.restrict Ω) := by
  apply memLp_top_of_bound
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp
      (measurable_fderiv ℝ b)).aestronglyMeasurable _
  exact Eventually.of_forall (lipschitz_gradient_bound hb)

lemma continuous_closure_memLp_top {Ω : Set Plane} {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    (hf : ContinuousOn f (closure Ω)) : MemLp f ∞ (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable ho.measurableSet) C
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact hC x (subset_closure hx)

lemma ambientSmooth_uniform_bound {Ω : Set Plane} (hΩ : Bornology.IsBounded Ω)
    {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ Ω, ‖ambientSmooth (planeApproxBump n) b x‖ ≤ C := by
  obtain ⟨M,hM⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hb.continuous.continuousOn
  refine ⟨max M 0+L,by positivity,fun n x hx => ?_⟩
  have he := ambientSmooth_error (planeApproxBump n) hb x
  have hφ := mul_le_mul_of_nonneg_left (planeApproxBump_rOut_le_one n) L.coe_nonneg
  have hx' := hM x (subset_closure hx)
  calc
    _ ≤ ‖ambientSmooth (planeApproxBump n) b x-b x‖+‖b x‖ := norm_le_norm_sub_add _ _
    _ ≤ (L:ℝ)+max M 0 := by linarith [le_max_left M 0]
    _ = _ := by ring



lemma HasH1Gradient.mul_lipschitz {Ω : Set Plane} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : HasH1Gradient Ω u g) {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    HasH1Gradient Ω (fun x => b x*u x) (fun x => b x • g x+u x • gradient b x) := by
  let bn := fun n => ambientSmooth (planeApproxBump n) b
  have hbn (n : ℕ) : ContDiff ℝ ∞ (bn n) := ambientSmooth_smooth _ hb
  have hbl (n : ℕ) : LipschitzWith L (bn n) := ambientSmooth_lipschitz _ hb
  have hb0 := continuous_closure_memLp_top ho hΩ hb.continuous.continuousOn
  have hb1 := lipschitz_gradient_memLp_top (Ω:=Ω) hb
  have hn0 (n : ℕ) := continuous_closure_memLp_top ho hΩ (hbl n).continuous.continuousOn
  have hn1 (n : ℕ) := lipschitz_gradient_memLp_top (Ω:=Ω) (hbl n)
  have hf (n : ℕ) := hu.mul_smooth (hbn n) (hn0 n) (hn1 n)
  have hv : MemLp (fun x => b x*u x) 2 (volume.restrict Ω) := hb0.fun_mul hu.1
  have hg : MemLp (fun x => b x • g x+u x • gradient b x) 2 (volume.restrict Ω) :=
    (hb0.smul hu.2.1).add (hu.1.smul hb1)
  obtain ⟨C,hC,hbd⟩ := ambientSmooth_uniform_bound hΩ hb
  have ht (x : Plane) : Tendsto (fun n => bn n x) atTop (𝓝 (b x)) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb x
  have hgt : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => gradient (bn n) x)
      atTop (𝓝 (gradient b x)) :=
    ae_restrict_of_ae (ambientSmooth_gradient_tendsto planeApproxBump_rOut_tendsto
      (Eventually.of_forall planeApproxBump_ratio) hb)
  apply HasH1Gradient.of_tendsto_L2 hf hv hg
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).1) hv
      (hu.1.norm.const_mul C)
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (ht x).mul_const (u x)
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).2.1) hg
      ((hu.2.1.norm.const_mul C).add (hu.1.norm.const_mul (L:ℝ)))
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      calc
        _ ≤ ‖bn n x • g x‖+‖u x • gradient (bn n) x‖ := norm_add_le _ _
        _ = ‖bn n x‖*‖g x‖+‖u x‖*‖gradient (bn n) x‖ := by rw [norm_smul,norm_smul]
        _ ≤ C*‖g x‖+‖u x‖*(L:ℝ) := add_le_add
          (mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (lipschitz_gradient_bound (hbl n) x) (norm_nonneg _))
        _ = _ := by simp only [Pi.add_apply]; ring
    · filter_upwards [hgt] with x hx
      exact ((ht x).smul_const (g x)).add (tendsto_const_nhds.smul hx)

namespace H1
variable {Ω : Set Plane} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)

def lipschitzMul (u : H1 Ω) : H1 Ω :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).toH1

lemma lipschitzMul_value_ae (u : H1 Ω) : H1.value (lipschitzMul ho hΩ hb u) =ᵐ[volume.restrict Ω]
    fun x => b x*H1.value u x :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).1.coeFn_toLp

lemma lipschitzMul_grad_ae (u : H1 Ω) : H1.grad (lipschitzMul ho hΩ hb u) =ᵐ[volume.restrict Ω]
    fun x => b x • H1.grad u x+H1.value u x • gradient b x :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).2.1.coeFn_toLp
end H1

end StrictHotSpots
end
end LipschitzH1

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)
local instance : NormedAddCommGroup (H10 ho) := H10.normedAddCommGroup ho
local instance : InnerProductSpace ℝ (H10 ho) := H10.innerProductSpace ho
local instance : CompleteSpace (H10 ho) := H10.completeSpace ho
local instance : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace

def pair (μ : ℝ) : H1 Ω →L[ℝ] H1 Ω →L[ℝ] ℝ :=
  ((innerSL ℝ).comp H1.grad).flip.comp H1.grad -
    μ • ((innerSL ℝ).comp H1.value).flip.comp H1.value

lemma pair_apply (μ : ℝ) (u v : H1 Ω) : pair μ u v =
    inner ℝ (H1.grad v) (H1.grad u)-μ*inner ℝ (H1.value v) (H1.value u) := rfl

lemma pair_comm (μ : ℝ) (u v : H1 Ω) : pair μ u v=pair μ v u := by
  rw [pair_apply,pair_apply]
  exact congrArg₂ (fun a b : ℝ => a-μ*b)
    (real_inner_comm (H1.grad u) (H1.grad v))
    (real_inner_comm (H1.value u) (H1.value v))

def incl : H10 ho →L[ℝ] H1 Ω := (h10Submodule ho).subtypeL

def zeroPair (μ : ℝ) : H10 ho →L[ℝ] H10 ho →L[ℝ] ℝ := by
  let a : H10 ho →L[ℝ] H1 Ω →L[ℝ] ℝ := (pair μ).comp (incl ho)
  let b : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 ho) (F := H1 Ω) a
  exact b.comp (incl ho)

lemma zeroPair_apply (μ : ℝ) (u v : H10 ho) : zeroPair ho μ u v =
    inner ℝ (H10.grad ho u) (H10.grad ho v)-μ*inner ℝ (H10.value ho u) (H10.value ho v) := rfl

lemma zeroPair_pair (μ : ℝ) (u v : H10 ho) : zeroPair ho μ u v=pair μ v.val u.val := rfl

lemma zeroPair_self (μ : ℝ) (v : H10 ho) : zeroPair ho μ v v=
    ‖H10.grad ho v‖^2-μ*‖H10.value ho v‖^2 :=
  (zeroPair_apply ho μ v v).trans (congrArg₂ (fun a b : ℝ => a-μ*b)
    (real_inner_self_eq_norm_sq (H10.grad ho v))
    (real_inner_self_eq_norm_sq (H10.value ho v)))

lemma subcritical_numeric {μ L C x y z : ℝ} (hμ : 0 ≤ μ) (hl : μ < L)
    (hv : C*x*x ≤ z^2) (hd : L*y^2 ≤ z^2) :
    ((1-μ/L)*C)*x*x ≤ z^2-μ*y^2 := by
  have hL : 0 < L := lt_of_le_of_lt hμ hl
  have hρ : 0 < 1-μ/L := sub_pos.mpr ((div_lt_one hL).mpr hl)
  have hmul := mul_le_mul_of_nonneg_left hd (div_nonneg hμ hL.le)
  have he : μ/L*(L*y^2)=μ*y^2 := by field_simp [ne_of_gt hL]
  rw [he] at hmul
  have hh := mul_le_mul_of_nonneg_left hv hρ.le
  nlinarith

lemma zeroPair_coercive (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    @IsCoercive (H10 ho) (H10.normedAddCommGroup ho).toSeminormedAddCommGroup
      (H10.innerProductSpace ho).toNormedSpace (zeroPair ho μ) := by
  obtain ⟨C,hC,hE⟩ := H10.energy_coercive ho hb
  have hL : 0 < L := lt_of_le_of_lt hμ hl
  have hρ : 0 < 1-μ/L := sub_pos.mpr ((div_lt_one hL).mpr hl)
  refine ⟨(1-μ/L)*C,mul_pos hρ hC,fun v => ?_⟩
  have hv : C*‖v‖*‖v‖ ≤ ‖H10.grad ho v‖^2 :=
    (hE v).trans_eq (by rw [H10.energy_apply,real_inner_self_eq_norm_sq])
  exact (subcritical_numeric hμ hl hv (hD v)).trans_eq
    (zeroPair_self ho μ v).symm

def forcing (μ : ℝ) : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := by
  let a : H10 ho →L[ℝ] H1 Ω →L[ℝ] ℝ := (pair μ).flip.comp (incl ho)
  let b : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 ho) (F := H1 Ω) a
  exact -b

def correction (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    H1 Ω →L[ℝ] H10 ho :=
  (zeroPair_coercive ho hb hμ hl hD).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    ((InnerProductSpace.toDual ℝ (H10 ho)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (forcing ho μ))

def extension (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    H1 Ω →L[ℝ] H1 Ω :=
  ContinuousLinearMap.id ℝ (H1 Ω)+(incl ho).comp (correction ho hb hμ hl hD)

lemma correction_spec (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (a : H1 Ω) (v : H10 ho) :
    zeroPair ho μ (correction ho hb hμ hl hD a) v = -pair μ a v.val := by
  rw [← (zeroPair_coercive ho hb hμ hl hD).continuousLinearEquivOfBilin_apply]
  simp only [correction,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

lemma extension_class (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) (a : H1 Ω) :
    ∃ w : H10 ho, extension ho hb hμ hl hD a-a=w.val := by
  exact ⟨correction ho hb hμ hl hD a,add_sub_cancel_left _ _⟩

lemma extension_weak (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) (a : H1 Ω)
    (v : H10 ho) : pair μ (extension ho hb hμ hl hD a) v.val=0 := by
  change pair μ (a+(correction ho hb hμ hl hD a).val) v.val=0
  rw [map_add,add_apply]
  have he := correction_spec ho hb hμ hl hD a v
  have hh : pair μ (correction ho hb hμ hl hD a).val v.val=
      zeroPair ho μ (correction ho hb hμ hl hD a) v := by
    exact (pair_comm μ _ _).trans (zeroPair_pair ho μ _ _).symm
  rw [hh,he,add_neg_cancel]

lemma norm_zero_numeric {C x : ℝ} (hC : 0 < C) (hx : 0 ≤ x) (h : C*x*x ≤ 0) : x=0 := by
  by_contra hn
  have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hn)
  exact (not_le_of_gt (mul_pos (mul_pos hC hp) hp)) h

lemma self_zero (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (w : H10 ho) (hz : zeroPair ho μ w w=0) : w=0 := by
  obtain ⟨C,hC,hB⟩ := zeroPair_coercive ho hb hμ hl hD
  have hn := hB w
  rw [hz] at hn
  exact norm_eq_zero.mp (norm_zero_numeric hC (norm_nonneg w) hn)

lemma pair_sub (μ : ℝ) (a b v : H1 Ω) :
    pair μ (a-b) v = pair μ a v-pair μ b v := by
  exact congrArg (fun t : H1 Ω →L[ℝ] ℝ => t v) ((pair μ).map_sub a b)

lemma unique (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    {a b : H1 Ω} (ha : ∀ v : H10 ho, pair μ a v.val=0)
    (hb' : ∀ v : H10 ho, pair μ b v.val=0)
    (hab : ∃ w : H10 ho, a-b=w.val) : a=b := by
  obtain ⟨w,hw⟩ := hab
  have h0 : pair μ w.val w.val=0 := by
    calc
      _ = pair μ (a-b) w.val := congrArg (fun z : H1 Ω => pair μ z w.val) hw.symm
      _ = pair μ a w.val-pair μ b w.val := pair_sub μ a b w.val
      _ = 0 := by rw [ha,hb',sub_self]
  have hz : zeroPair ho μ w w=0 := h0
  have hw0 : w=0 := self_zero ho hb hμ hl hD w hz
  apply sub_eq_zero.mp
  exact hw.trans (congrArg (fun z : H10 ho => z.val) hw0)

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section PhysicalSolutionWeak

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

lemma inner_H1grad_add_single {S : Set Plane} (a b z : H1 S) :
    inner ℝ (H1.grad (a+b)) (H1.grad z) =
    inner ℝ (H1.grad a) (H1.grad z)+inner ℝ (H1.grad b) (H1.grad z) := by
  rw [map_add,inner_add_left]

include d hd hb in
lemma affine_H10_grad_pair {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (u v : H10 e.open_source) :
    inner ℝ (H1.grad (hW.toH1+(transportH10 e he u).val))
      (H10.grad e.open_target (transportH10 e he v)) =
    inner ℝ (H1.grad (hV.toH1+u.val)) (H10.grad e.open_source v) := by
  exact (inner_H1grad_add_single hW.toH1 (transportH10 e he u).val
    (transportH10 e he v).val).trans
      ((congrArg₂ (fun a b : ℝ => a+b) (transportH10_mixed_grad e he d hd hb hw hW hV v)
        (transportH10_inner_grad e he d hd hb u v)).trans
          (inner_H1grad_add_single hV.toH1 u.val v.val).symm)

include hd hb in
lemma affine_H10_mass_pair {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (u v : H10 e.open_source) :
    inner ℝ (H1.value (hW.toH1+(transportH10 e he u).val))
      (H10.value e.open_target (transportH10 e he v)) =
    ∫ x, H1.value (hV.toH1+u.val) x*H10.value e.open_source v x ∂chartMeasure e d :=
  isometry_value_pair (chartPull e d hd) _ _
    (affine_value_ae e he d hd hb hW hV u) (weightedValue_ae e he d hd hb v).symm

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma physicalSolution_mixed_grad {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (v : H10 diskOpen) :
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H10.grad c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) =
    inner ℝ (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl)) (H10.grad diskOpen v) := by
  have hh := affine_H10_grad_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp))
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw) (c.pullDatum_comp_H1 hb hs hw)
    (c.datumCorrection hb hs hμ hw hl) v
  apply hh.trans
  apply congrArg (fun U : H1 disk => inner ℝ (H1.grad U) (H10.grad diskOpen v))
  exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
    (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm

lemma physicalSolution_mixed_mass {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (v : H10 diskOpen) :
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H10.value c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) =
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl))
      (H10.weightedValue diskOpen c.densityBound_ne_top (c.density_bound hμ) v) := by
  have hh := affine_H10_mass_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw) (c.pullDatum_comp_H1 hb hs hw)
    (c.datumCorrection hb hs hμ hw hl) v
  have he : (c.pullDatum_comp_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val=
      boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  let S := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  have hr := congrArg (fun U : H1 disk =>
    ∫ x, H1.value U x*H10.value diskOpen v x ∂chartMeasure c.diskMap c.d) he
  have hp := potentialMeasure_integral c.diskMap c.d hμ
    (fun x => H1.value S x*H10.value diskOpen v x)
  have hq := congrArg (fun ν : Measure Plane => ∫ x,
    H1.value S x*H10.value diskOpen v x ∂ν) c.potential_diskMap
  exact (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr)).trans
    (hp.symm.trans (hq.trans (observe_inner c.densityBound_ne_top (c.density_bound hμ) S v.val).symm))

lemma pair_forward {S : Set Plane} (μ : ℝ) (u v : H1 S) :
    PhysicalHelmholtz.pair μ u v = inner ℝ (H1.grad u) (H1.grad v)-
      μ*inner ℝ (H1.value u) (H1.value v) :=
  (PhysicalHelmholtz.pair_comm μ u v).trans (PhysicalHelmholtz.pair_apply μ v u)

lemma physicalSolution_transported_weak (hne : Ω.Nonempty) (hpos : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (t : H10 diskOpen) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl)
      (show H1 Ω from (transportH10 c.diskMap c.diskMap_inverse_smooth t).val)=0 := by
  have hn := c.operator_norm_lt_one hb hne hpos
  have hwk := boundarySolution_weak c.densityBound_ne_top (c.density_bound hμ) hn
    (c.datumTrace w hw.continuousOn) hl t
  have hg := c.physicalSolution_mixed_grad hb hs hμ hw hl t
  have hm := c.physicalSolution_mixed_mass hb hs hμ hw hl t
  exact (pair_forward _ _ _).trans (sub_eq_zero.mpr (hg.trans (hwk.trans hm.symm)))

lemma physicalSolution_weak (hne : Ω.Nonempty) (hpos : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (v : H10 (show IsOpen Ω from c.diskMap.open_target)) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl) v.val=0 := by
  let t : H10 diskOpen := transportH10 c.diskMap.symm c.diskMap_smooth v
  have ht : transportH10 c.diskMap c.diskMap_inverse_smooth t=v :=
    transportH10_symm c.diskMap.symm c.diskMap_smooth c.diskMap_inverse_smooth c.d' c.d
      c.diskMap_inverse_deriv c.diskMap_deriv diskBounded hb v
  have he := c.physicalSolution_transported_weak hb hs hμ hne hpos hw hl t
  exact (congrArg (fun V : H10 (show IsOpen Ω from c.diskMap.open_target) =>
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl) V.val) ht).symm.trans he

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end PhysicalSolutionWeak

section LipschitzH1Convergence

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots

lemma H1.tendsto_of_components {Ω : Set Plane} {v : ℕ → H1 Ω} {u : H1 Ω}
    (hv : Tendsto (fun n => H1.value (v n)) atTop (𝓝 (H1.value u)))
    (hg : Tendsto (fun n => H1.grad (v n)) atTop (𝓝 (H1.grad u))) :
    Tendsto v atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hv.prodMk_nhds hg)

lemma smoothMul_tendsto_lipschitzMul {Ω : Set Plane} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)
    (u : H1 Ω) :
    Tendsto (fun n => H1.smoothMul (ambientSmooth_smooth (planeApproxBump n) hb)
      (continuous_closure_memLp_top ho hΩ (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
      (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb)) u)
      atTop (𝓝 (H1.lipschitzMul ho hΩ hb u)) := by
  let bn := fun n => ambientSmooth (planeApproxBump n) b
  have hbn (n : ℕ) : ContDiff ℝ ∞ (bn n) := ambientSmooth_smooth _ hb
  have hbl (n : ℕ) : LipschitzWith L (bn n) := ambientSmooth_lipschitz _ hb
  have hn0 (n : ℕ) := continuous_closure_memLp_top ho hΩ (hbl n).continuous.continuousOn
  have hn1 (n : ℕ) := lipschitz_gradient_memLp_top (Ω:=Ω) (hbl n)
  have hu := H1.hasH1Gradient u
  have hf (n : ℕ) := hu.mul_smooth (hbn n) (hn0 n) (hn1 n)
  have hl := hu.mul_lipschitz ho hΩ hb
  obtain ⟨C,hC,hbd⟩ := ambientSmooth_uniform_bound hΩ hb
  have ht (x : Plane) : Tendsto (fun n => bn n x) atTop (𝓝 (b x)) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb x
  have hgt : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => gradient (bn n) x)
      atTop (𝓝 (gradient b x)) :=
    ae_restrict_of_ae (ambientSmooth_gradient_tendsto planeApproxBump_rOut_tendsto
      (Eventually.of_forall planeApproxBump_ratio) hb)
  apply H1.tendsto_of_components
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).1) hl.1
      (hu.1.norm.const_mul C)
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (ht x).mul_const (H1.value u x)
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).2.1) hl.2.1
      ((hu.2.1.norm.const_mul C).add (hu.1.norm.const_mul (L:ℝ)))
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      calc
        _ ≤ ‖bn n x • H1.grad u x‖+‖H1.value u x • gradient (bn n) x‖ := norm_add_le _ _
        _ = ‖bn n x‖*‖H1.grad u x‖+‖H1.value u x‖*‖gradient (bn n) x‖ := by rw [norm_smul,norm_smul]
        _ ≤ C*‖H1.grad u x‖+‖H1.value u x‖*(L:ℝ) := add_le_add
          (mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (lipschitz_gradient_bound (hbl n) x) (norm_nonneg _))
        _ = _ := by simp only [Pi.add_apply]; ring
    · filter_upwards [hgt] with x hx
      exact ((ht x).smul_const (H1.grad u x)).add (tendsto_const_nhds.smul hx)

end StrictHotSpots
end
end LipschitzH1Convergence

section LipschitzVectorMultiplier

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane} (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
variable {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)

theorem boundaryDefect_lipschitz_multiplier (X : Fin 2 → H1 Ω) :
    boundaryDefect (fun i => H1.lipschitzMul ho hbound hb (X i))
      (fun i => H1.lipschitzMul ho hbound hb (X i)) =
    boundaryDefect X (fun i => H1.lipschitzMul ho hbound hb (H1.lipschitzMul ho hbound hb (X i))) := by
  rw [boundaryDefect_integral,boundaryDefect_integral]
  apply integral_congr_ae
  let M := H1.lipschitzMul ho hbound hb
  filter_upwards [H1.lipschitzMul_grad_ae ho hbound hb (X 0),
    H1.lipschitzMul_grad_ae ho hbound hb (X 1),
    H1.lipschitzMul_value_ae ho hbound hb (X 0),
    H1.lipschitzMul_value_ae ho hbound hb (X 1),
    H1.lipschitzMul_grad_ae ho hbound hb (M (X 0)),
    H1.lipschitzMul_grad_ae ho hbound hb (M (X 1))] with x h0 h1 hv0 hv1 hh0 hh1
  change H1.grad (M (X 0)) x = _ at h0
  change H1.grad (M (X 1)) x = _ at h1
  change H1.value (M (X 0)) x = _ at hv0
  change H1.value (M (X 1)) x = _ at hv1
  change -inner ℝ (H1.grad (M (X 0)) x) (rot (H1.grad (M (X 1)) x))+
      inner ℝ (H1.grad (M (X 1)) x) (rot (H1.grad (M (X 0)) x)) = _
  exact defect_multiplier_substitute (b x) (H1.value (X 0) x) (H1.value (X 1) x)
    (H1.value (M (X 0)) x) (H1.value (M (X 1)) x)
    (H1.grad (X 0) x) (H1.grad (X 1) x) (gradient b x)
    (H1.grad (M (X 0)) x) (H1.grad (M (X 1)) x)
    (H1.grad (M (M (X 0))) x) (H1.grad (M (M (X 1))) x)
    h0 h1 hv0 hv1 hh0 hh1

lemma vectorValue_lipschitzMul_ae (X : Fin 2 → H1 Ω) :
    vectorValue (fun i => H1.lipschitzMul ho hbound hb (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x • vectorValue X x := by
  let M := H1.lipschitzMul ho hbound hb
  filter_upwards [vectorValue_ae (fun i => M (X i)),vectorValue_ae X,
    H1.lipschitzMul_value_ae ho hbound hb (X 0),H1.lipschitzMul_value_ae ho hbound hb (X 1)]
      with x hV hX h0 h1
  apply hV.trans
  exact (congrArg₂ (fun a d : ℝ => a • e 0+d • e 1) h0 h1).trans
    (by rw [hX]; module)

lemma divergenceL_lipschitzMul_ae (X : Fin 2 → H1 Ω) :
    divergenceL (fun i => H1.lipschitzMul ho hbound hb (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x*divergenceL X x+inner ℝ (vectorValue X x) (gradient b x) := by
  let M := H1.lipschitzMul ho hbound hb
  filter_upwards [divergenceL_ae (fun i => M (X i)),divergenceL_ae X,vectorValue_ae X,
    H1.lipschitzMul_grad_ae ho hbound hb (X 0),H1.lipschitzMul_grad_ae ho hbound hb (X 1)]
      with x hD hX hV h0 h1
  apply hD.trans
  exact (congrArg₂ (fun A B : Plane => c 0 A+c 1 B) h0 h1).trans
    ((divergence_multiplier_algebra _ _ _ _ _ _).trans
      (congrArg₂ (fun d : ℝ => fun V : Plane => b x*d+inner ℝ V (gradient b x)) hX hV).symm)


lemma normal_pair_lipschitzMul (X : Fin 2 → H1 Ω) (u : H1 Ω) :
    inner ℝ (vectorValue (fun i => H1.lipschitzMul ho hbound hb (X i))) (H1.grad u)+
      inner ℝ (divergenceL (fun i => H1.lipschitzMul ho hbound hb (X i))) (H1.value u) =
    inner ℝ (vectorValue X) (H1.grad (H1.lipschitzMul ho hbound hb u))+
      inner ℝ (divergenceL X) (H1.value (H1.lipschitzMul ho hbound hb u)) := by
  refine Eq.trans (normal_pair_integral _ _) (Eq.trans ?_ (normal_pair_integral _ _).symm)
  apply integral_congr_ae
  filter_upwards [vectorValue_lipschitzMul_ae ho hbound hb X,divergenceL_lipschitzMul_ae ho hbound hb X,
    H1.lipschitzMul_grad_ae ho hbound hb u,H1.lipschitzMul_value_ae ho hbound hb u] with x hV hD hG hu
  exact (congrArg₂ (fun V : Plane => fun F : ℝ =>
    inner ℝ V (H1.grad u x)+F*H1.value u x) hV hD).trans
      ((normal_multiplier_algebra _ _ _ _ _ _).trans
        (congrArg₂ (fun G : Plane => fun v : ℝ => inner ℝ (vectorValue X x) G+divergenceL X x*v) hG hu).symm)


theorem TangentWeak.lipschitzMul {X : Fin 2 → H1 Ω} (hX : TangentWeak X) :
    TangentWeak (fun i => H1.lipschitzMul ho hbound hb (X i)) := by
  intro u
  have he := normal_pair_lipschitzMul ho hbound hb X u
  have hz := hX (H1.lipschitzMul ho hbound hb u)
  linarith only [he,hz]

theorem boundaryClass_lipschitz_multiplier_identity (μ : ℝ) (X Y Z : Fin 2 → H1 Ω)
    (hX : TangentWeak X)
    (hY : ∀ i, ∃ w : H10 ho, Y i-H1.lipschitzMul ho hbound hb (X i)=w.val)
    (hZ : ∀ i, ∃ w : H10 ho,
      Z i-H1.lipschitzMul ho hbound hb (H1.lipschitzMul ho hbound hb (X i))=w.val)
    (hpos : ∀ V : Fin 2 → H1 Ω, TangentWeak V → 0 ≤ vectorForm μ V V)
    (hnull : vectorForm μ X X=0) :
    vectorForm μ Y Y=cartesianForm μ Y Y-cartesianForm μ X Z := by
  let M := H1.lipschitzMul ho hbound hb
  have htZ : TangentWeak Z := TangentWeak.of_class ho
    ((hX.lipschitzMul ho hbound hb).lipschitzMul ho hbound hb) hZ
  have hz : vectorForm μ X Z=0 := vectorForm_null_pair μ X Z hX htZ hpos hnull
  have hYY : boundaryDefect Y Y = boundaryDefect (fun i => M (X i)) (fun i => M (X i)) :=
    boundaryDefect_class ho Y Y _ _ hY hY
  have hZZ : boundaryDefect X Z = boundaryDefect X (fun i => M (M (X i))) :=
    boundaryDefect_class_right ho X Z _ hZ
  have he : boundaryDefect Y Y = boundaryDefect X Z :=
    hYY.trans ((boundaryDefect_lipschitz_multiplier ho hbound hb X).trans hZZ.symm)
  have hqY := vectorForm_eq_cartesian_add_defect μ Y Y
  have hqZ := vectorForm_eq_cartesian_add_defect μ X Z
  linarith only [hqY,hqZ,he,hz]


end StrictHotSpots.Hodge
end
end LipschitzVectorMultiplier

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma scalarSolution_weak {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (v : H10 hΩ.2.1) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω)
      (c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw) v.val=0 :=
  c.physicalSolution_weak hΩ.2.2.1 hΩ.2.2.2.2 hμ.le hΩ.1 hμ hw _ v

lemma class_difference {S : Set Plane} (ho : IsOpen S) {a b f : H1 S}
    (ha : ∃ v : H10 ho, a-f=v.val) (hb : ∃ v : H10 ho, b-f=v.val) :
    ∃ v : H10 ho, a-b=v.val := by
  obtain ⟨v,hv⟩ := ha
  obtain ⟨w,hw⟩ := hb
  refine ⟨v-w,?_⟩
  change a-b=v.val-w.val
  exact (show a-b=(a-f)-(b-f) from by abel).trans
    (congrArg₂ (fun x y : H1 S => x-y) hv hw)

lemma scalarSolution_eq_extension {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw =
      PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1 := by
  apply PhysicalHelmholtz.unique hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
    (c.scalarSolution_weak hΩ hμ hw)
    (PhysicalHelmholtz.extension_weak hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _)
  exact class_difference hΩ.2.1 (c.scalarSolution_class hΩ.2.2.1 hΩ.2.2.2.2 hμ hw)
    (PhysicalHelmholtz.extension_class hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _)

lemma multipliedGradient_eq_extension {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (i : Fin 2) : c.multipliedGradient hΩ hu hμ hb i =
      PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (H1.smoothMul hb hb0 hb1 (eigenGradientField hΩ hu i)) := by
  have hh := c.scalarSolution_eq_extension hΩ hμ hl hD
    (hb.contDiffOn.mul (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)))
  have he := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hb hb0 hb1
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i))
  exact hh.trans (congrArg (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD) he.symm)


def lipschitzMultipliedGradient {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) : Fin 2 → H1 Ω := fun i =>
  PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
    (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i))

lemma multipliedGradient_tendsto {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) (i : Fin 2) :
    Tendsto (fun n => c.multipliedGradient hΩ hu hμ (ambientSmooth_smooth (planeApproxBump n) hb) i)
      atTop (𝓝 (lipschitzMultipliedGradient hΩ hμ hl hD hu hb i)) := by
  have ht := (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD).continuous.continuousAt.tendsto.comp
    (smoothMul_tendsto_lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i))
  apply ht.congr'
  exact Eventually.of_forall fun n => (c.multipliedGradient_eq_extension hΩ hμ hl hD hu
    (ambientSmooth_smooth (planeApproxBump n) hb)
    (continuous_closure_memLp_top hΩ.2.1 hΩ.2.2.1
      (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
    (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb)) i).symm

lemma lipschitzMultipliedGradient_class {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) (i : Fin 2) :
    ∃ w : H10 hΩ.2.1, lipschitzMultipliedGradient hΩ hμ hl hD hu hb i-
      H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i)=w.val :=
  PhysicalHelmholtz.extension_class hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _

lemma lipschitzMultipliedGradient_tangent {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    TangentWeak (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) :=
  TangentWeak.of_class hΩ.2.1 ((eigenGradientField_null hΩ hu).1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb)
    (lipschitzMultipliedGradient_class hΩ hμ hl hD hu hb)

end StrictHotSpots.Conformal.ClosedDiskChart

namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}
lemma vectorForm_tendsto {X : ℕ → Fin 2 → H1 Ω} {Y : Fin 2 → H1 Ω}
    (h : ∀ i, Tendsto (fun n => X n i) atTop (𝓝 (Y i))) (μ : ℝ) :
    Tendsto (fun n => vectorForm μ (X n) (X n)) atTop (𝓝 (vectorForm μ Y Y)) := by
  have hg (i : Fin 2) := H1.grad.continuous.continuousAt.tendsto.comp (h i)
  have hv (i : Fin 2) := H1.value.continuous.continuousAt.tendsto.comp (h i)
  have hp (i j : Fin 2) := (coordinateL Ω i).continuous.continuousAt.tendsto.comp (hg j)
  have ha (i : Fin 2) := (axisL Ω i).continuous.continuousAt.tendsto.comp (hv i)
  have hd := (hp 0 0).add (hp 1 1)
  have hc := (hp 0 1).sub (hp 1 0)
  have hb := (ha 0).add (ha 1)
  exact ((hd.inner hd).add (hc.inner hc)).sub ((hb.inner hb).const_mul μ)
end StrictHotSpots.Hodge
end
end PhysicalMultiplierLimit

section MultiplierKernelConvergence

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma harmonic_square_bound {b : Boundary → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) (s t : Boundary) :
    ‖boundaryInteraction s t*(b s-b t)^2‖ ≤ (B:ℝ)*B/Real.pi := by
  simpa only [Real.inner_apply,pow_two] using harmonic_boundary_bound hb hb s t

lemma multiplier_integrand_bound {R : Boundary → Boundary → ℝ}
    {g : Boundary → E} {b : Boundary → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) {M G : ℝ} (_hM : 0 ≤ M) (hG : 0 ≤ G)
    (hbM : ∀ s, ‖b s‖ ≤ M) (hgG : ∀ s, ‖g s‖ ≤ G) (s t : Boundary) :
    ‖(boundaryInteraction s t+R s t)*(b s-b t)^2*inner ℝ (g s) (g t)‖ ≤
      ((B:ℝ)*B/Real.pi+(M+M)^2*‖R s t‖)*(G*G) := by
  have hd : ‖b s-b t‖ ≤ M+M := (norm_sub_le _ _).trans (add_le_add (hbM s) (hbM t))
  have hi : ‖inner ℝ (g s) (g t)‖ ≤ G*G :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hgG s) (hgG t) (norm_nonneg _) hG)
  have hr : ‖R s t*(b s-b t)^2‖ ≤ (M+M)^2*‖R s t‖ := by
    rw [norm_mul,norm_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hd 2) (norm_nonneg _)
  have he : (boundaryInteraction s t+R s t)*(b s-b t)^2 =
      boundaryInteraction s t*(b s-b t)^2+R s t*(b s-b t)^2 := by ring
  rw [he,norm_mul]
  exact mul_le_mul ((norm_add_le _ _).trans (add_le_add (harmonic_square_bound hb s t) hr))
    hi (norm_nonneg _) (by positivity)




theorem multiplier_kernel_tendsto {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → E} (hg : Continuous g) {b : Boundary → ℝ} {bn : ℕ → Boundary → ℝ}
    {B : ℝ≥0} (hb : ∀ n, LipschitzWith B (bn n)) {M : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ n s, ‖bn n s‖ ≤ M) (ht : ∀ s, Tendsto (fun n => bn n s) atTop (𝓝 (b s))) :
    Tendsto (fun n => ∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*(bn n z.1-bn n z.2)^2*
        inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure) atTop
      (𝓝 (∫ z : Boundary × Boundary,
        (boundaryInteraction z.1 z.2+R z.1 z.2)*(b z.1-b z.2)^2*
          inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)) := by
  obtain ⟨G,hG,hGb⟩ := boundary_continuous_bound hg
  apply tendsto_integral_of_dominated_convergence
    (fun z : Boundary × Boundary => ((B:ℝ)*B/Real.pi+(M+M)^2*‖R z.1 z.2‖)*(G*G))
  · intro n
    exact ((boundaryInteraction_measurable.aestronglyMeasurable.add hR.aestronglyMeasurable).mul
      ((((hb n).continuous.comp continuous_fst).sub ((hb n).continuous.comp continuous_snd)).pow 2).aestronglyMeasurable).mul
        ((hg.comp continuous_fst).inner (hg.comp continuous_snd)).aestronglyMeasurable
  · exact ((integrable_const _).add (hR.norm.const_mul ((M+M)^2))).mul_const (G*G)
  · intro n
    exact Eventually.of_forall fun z => multiplier_integrand_bound (hb n) hM hG (hMb n) hGb z.1 z.2
  · exact Eventually.of_forall fun z =>
      ((((ht z.1).sub (ht z.2)).pow 2).const_mul _).mul_const _

end StrictHotSpots.PlaneGreen
end
end MultiplierKernelConvergence

section ScalarBoundaryForm

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma scalarSolution_form (hne : Ω.Nonempty)
    {w z : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hz : ContDiffOn ℝ ∞ z (closure Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    H1.form (firstPositiveNeumannValue Ω) (c.scalarSolution hb hs hμ hw)
      (c.scalarSolution hb hs hμ hz) =
    boundaryForm (fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le)) 0
      (fun s : Boundary => w (c.F s)) (fun s : Boundary => z (c.F s)) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  have he := c.scalarSolution_energy hb hs hμ hne hw hz
  simp only [boundaryForm,Pi.zero_apply,zero_mul,integral_zero,add_zero,
    RCLike.inner_apply,conj_trivial] at ⊢
  change _ = _
  rw [show H1.form (firstPositiveNeumannValue Ω) (c.scalarSolution hb hs hμ hw)
    (c.scalarSolution hb hs hμ hz) = _ from he]
  congr 1
  congr 1
  funext q
  ring

end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots.Hodge
lemma cartesianForm_eq_sum {Ω : Set Plane} (μ : ℝ) (X Y : Fin 2 → H1 Ω) :
    cartesianForm μ X Y=H1.form μ (X 0) (Y 0)+H1.form μ (X 1) (Y 1) := by
  simp only [cartesianForm,cartesianEnergy,H1.form]
  ring
end StrictHotSpots.Hodge
end
end ScalarBoundaryForm

section SmoothMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma multipliedGradient_coordinate_difference {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    H1.form (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb i)
      (c.multipliedGradient hΩ hu hμ hb i)-
    H1.form (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu i)
      (c.multipliedGradient hΩ hu hμ (hb.mul hb) i) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
        (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i)) ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let hw := closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)
  have hx : eigenGradientField hΩ hu i = c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw :=
    (c.scalarSolution_eq_of_helmholtz hΩ.2.2.1 hΩ.2.2.2.2 hμ hΩ.1 hw
      (fun _ hx => closed_directional_helmholtz hΩ.2.1 hu (Hodge.e i) hx)).symm
  rw [hx]
  change H1.form _ (c.scalarSolution _ _ hμ (hb.contDiffOn.mul hw))
    (c.scalarSolution _ _ hμ (hb.contDiffOn.mul hw))-
    H1.form _ (c.scalarSolution _ _ hμ hw)
      (c.scalarSolution _ _ hμ ((hb.contDiffOn.mul hb.contDiffOn).mul hw)) = _
  rw [c.scalarSolution_form _ _ _ hΩ.1,c.scalarSolution_form _ _ _ hΩ.1]
  obtain ⟨A,hA⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hb.contDiffOn
  change LipschitzWith A (fun s : Boundary => fderivWithin ℝ u (closure Ω) (c.F s) (Hodge.e i)) at hA
  change LipschitzWith B (fun s : Boundary => b (c.F s)) at hB
  exact (by simpa only [smul_eq_mul,pow_two] using
    (boundaryForm_multiplier_difference (c := (0 : Boundary → ℝ))
      (fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le))
      (fullBoundaryR_symm c.densityBound_ne_top (c.density_bound hμ.le)
        (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ)) hA hB))

lemma datum_multiplier_integrable {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hb : ContDiff ℝ ∞ b) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    Integrable (fun z : Boundary × Boundary =>
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2 * inner ℝ (w (c.F z.1)) (w (c.F z.2)))
      (boundaryMeasure.prod boundaryMeasure) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  obtain ⟨A,hA⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hb.contDiffOn
  change LipschitzWith A (fun s : Boundary => w (c.F s)) at hA
  change LipschitzWith B (fun s : Boundary => b (c.F s)) at hB
  have hR : Integrable (fun z : Boundary × Boundary =>
      fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)
      (boundaryMeasure.prod boundaryMeasure) :=
    fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le)
  exact multiplier_integrand_integrable (E := ℝ) (g := fun s : Boundary => w (c.F s))
    (b := fun s : Boundary => b (c.F s)) hR hA hB



theorem smooth_multiplier_kernel {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let T (i : Fin 2) (z : Boundary × Boundary) :=
    (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
        (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i))
  have hi (i : Fin 2) : Integrable (T i) (boundaryMeasure.prod boundaryMeasure) :=
    c.datum_multiplier_integrable hΩ hμ
      (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)) hb
  rw [c.multipliedGradient_identity hΩ hu hμ hb hb0 hb1,
    cartesianForm_eq_sum,cartesianForm_eq_sum]
  have h0 := c.multipliedGradient_coordinate_difference hΩ hu hμ hb 0
  have h1 := c.multipliedGradient_coordinate_difference hΩ hu hμ hb 1
  change _ = (1/2:ℝ)* _ at h0 h1
  have ha : (∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure)+
      (∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) =
      ∫ z : Boundary × Boundary,
        (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
        (b (c.F z.1)-b (c.F z.2))^2*
        inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
          ∂boundaryMeasure.prod boundaryMeasure := by
    rw [← integral_add (hi 0) (hi 1)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Hodge.inner_two]
    simp only [T,Hodge.c,closedGradient,
      InnerProductSpace.toDual_symm_apply,Real.inner_apply]
    ring
  change (∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure)+
    (∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) = _ at ha
  change _ = (1/2:ℝ)*(∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure) at h0
  change _ = (1/2:ℝ)*(∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) at h1
  linarith

include hu in

theorem smooth_multiplier_kernel_nonneg {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    0 ≤ (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  change 0 ≤ (1/2:ℝ) * _
  rw [← c.smooth_multiplier_kernel hΩ hu hμ hb hb0 hb1]
  exact c.multipliedGradient_nonneg hΩ hu hμ hb hb0 hb1
end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothMultiplierKernel

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include hΩ hu in
lemma closedGradient_trace_continuous :
    Continuous (fun s : Boundary => closedGradient Ω u (c.F s)) := by
  apply (closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1).comp_continuous
    (c.lipschitz.continuous.comp continuous_subtype_val)
  intro s
  exact c.maps_closed (boundary_mem_closed s)

lemma physical_boundary_lipschitz {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) : LipschitzWith ((B*c.Lip)*1)
      (fun s : Boundary => b (c.F s)) :=
  (hb.comp c.lipschitz).comp (LipschitzWith.subtype_val _)

include hΩ in
lemma smooth_physical_boundary_bound {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ n (s : Boundary),
      ‖ambientSmooth (planeApproxBump n) b (c.F s)‖ ≤ M := by
  have hc : Bornology.IsBounded (closure Ω) := hΩ.2.2.1.closure
  obtain ⟨M,hM,hMb⟩ := ambientSmooth_uniform_bound hc hb
  exact ⟨M,hM,fun n s => hMb n (c.F s) (c.maps_closed (boundary_mem_closed s))⟩

include hΩ in
lemma physical_multiplier_integral_tendsto
    {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2)
      (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → Plane} (hg : Continuous g)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    Tendsto (fun n => ∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*
      (ambientSmooth (planeApproxBump n) b (c.F z.1)-ambientSmooth (planeApproxBump n) b (c.F z.2))^2*
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure) atTop
      (𝓝 (∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*(b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)) := by
  let bn : ℕ → Boundary → ℝ := fun n s => ambientSmooth (planeApproxBump n) b (c.F s)
  have hn (n : ℕ) : LipschitzWith ((B*c.Lip)*1) (bn n) :=
    c.physical_boundary_lipschitz (ambientSmooth_lipschitz (planeApproxBump n) hb)
  obtain ⟨M,hM,hMb⟩ := c.smooth_physical_boundary_bound hΩ hb
  have hm (n : ℕ) (s : Boundary) : ‖bn n s‖ ≤ M := hMb n s
  have ht (s : Boundary) : Tendsto (fun n => bn n s) atTop (𝓝 (b (c.F s))) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb (c.F s)
  exact multiplier_kernel_tendsto (bn:=bn) (B:=(B*c.Lip)*1) hR hg hn hM hm ht



theorem lipschitz_multiplier_kernel {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hlhs := vectorForm_tendsto (c.multipliedGradient_tendsto hΩ hμ hl hD hu hb)
    (firstPositiveNeumannValue Ω)
  have hrhs := (c.physical_multiplier_integral_tendsto hΩ
    (fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le))
    (c.closedGradient_trace_continuous hΩ hu) hb).const_mul (1/2:ℝ)
  apply tendsto_nhds_unique hlhs
  apply hrhs.congr'
  exact Eventually.of_forall fun n => (c.smooth_multiplier_kernel hΩ hu hμ
    (ambientSmooth_smooth (planeApproxBump n) hb)
    (continuous_closure_memLp_top hΩ.2.1 hΩ.2.2.1
      (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
    (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb))).symm

lemma lipschitzMultipliedGradient_nonneg {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    0 ≤ vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) :=
  vectorForm_nonneg hΩ.2.1 hΩ.1 hΩ.2.2.2.1 hΩ.2.2.1 hμ hl hD _
    (lipschitzMultipliedGradient_tangent hΩ hμ hl hD hu hb)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel

section HilbertMultiplierSum

noncomputable section
open Set MeasureTheory Metric Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

lemma orthonormal_countable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] {e : ι → H} (he : Orthonormal ℝ e) : Countable ι := by
  have hp : Pairwise (Disjoint on fun i => ball (e i) (1/2:ℝ)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    have hd : dist (e i) (e j) < 1 := by
      have h := dist_triangle (e i) x (e j)
      have hi : dist (e i) x < 1/2 := by simpa [dist_comm] using hxi
      have hj : dist x (e j) < 1/2 := hxj
      linarith
    have hn : ‖e i-e j‖^2 = 2 := by
      rw [norm_sub_sq_real,he.1 i,he.1 j,he.2 hij]
      norm_num
    rw [dist_eq_norm] at hd
    nlinarith [norm_nonneg (e i-e j)]
  exact hp.countable_of_isOpen_disjoint (fun _ => isOpen_ball)
    (fun i => ⟨e i,mem_ball_self (by norm_num)⟩)

lemma coordinate_hasSum {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i => (inner ℝ (e i) x)^2) (‖x‖^2) := by
  have h := e.hasSum_inner_mul_inner x x
  simpa only [real_inner_comm x,← pow_two,real_inner_self_eq_norm_sq] using h



theorem coordinate_energy_sum {X H E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Countable ι] (μ : Measure X) [SFinite μ] (e : HilbertBasis ι ℝ H)
    (N : X → X → ℝ) (K : X → ℝ) (b : X → H) (g : X → E)
    (hN : ∀ s t, 0 ≤ N s t)
    (hidentity : ∀ᵐ z : X × X ∂μ.prod μ, N z.1 z.2 * ‖b z.1-b z.2‖^2 = K z.1*K z.2)
    (hKg : Integrable (fun s => K s • g s) μ)
    (hbound : Integrable (fun z : X × X =>
      N z.1 z.2 * ‖b z.1-b z.2‖^2 * (‖g z.1‖*‖g z.2‖)) (μ.prod μ))
    (hF : ∀ i, AEStronglyMeasurable (fun z : X × X => N z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 * inner ℝ (g z.1) (g z.2)) (μ.prod μ)) :
    HasSum (fun i => (1/2:ℝ) * ∫ z : X × X, N z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 * inner ℝ (g z.1) (g z.2) ∂μ.prod μ)
      ((1/2:ℝ)*‖∫ s, K s • g s ∂μ‖^2) := by
  let B : ι → X × X → ℝ := fun i z =>
    N z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 * (‖g z.1‖*‖g z.2‖)
  have hB (z : X × X) : HasSum (fun i => B i z)
      (N z.1 z.2 * ‖b z.1-b z.2‖^2 * (‖g z.1‖*‖g z.2‖)) :=
    ((coordinate_hasSum e (b z.1-b z.2)).mul_left (N z.1 z.2)).mul_right _
  have hsum := hasSum_integral_of_dominated_convergence (μ := μ.prod μ) B hF
    (fun i => Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (hN _ _),abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (mul_nonneg (hN _ _) (sq_nonneg _))))
    (Filter.Eventually.of_forall (fun z => (hB z).summable))
    (hbound.congr (Filter.Eventually.of_forall (fun z => (hB z).tsum_eq.symm)))
    (Filter.Eventually.of_forall (fun z =>
      ((coordinate_hasSum e (b z.1-b z.2)).mul_left (N z.1 z.2)).mul_right (inner ℝ (g z.1) (g z.2))))
  have hint : (∫ z : X × X, N z.1 z.2 * ‖b z.1-b z.2‖^2 *
      inner ℝ (g z.1) (g z.2) ∂μ.prod μ) = ‖∫ s, K s • g s ∂μ‖^2 := by
    calc
      _ = ∫ z : X × X, inner ℝ (K z.1 • g z.1) (K z.2 • g z.2) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [hidentity] with z hz
        rw [hz,real_inner_smul_left,real_inner_smul_right]
        ring
      _ = ∫ s, ∫ t, inner ℝ (K s • g s) (K t • g t) ∂μ ∂μ := by
        exact integral_prod _ (Integrable.op_fst_snd (op := inner ℝ) (continuous_fst.inner continuous_snd)
          ⟨1, fun x y => by simpa only [one_mul] using norm_inner_le_norm x y⟩ hKg hKg)
      _ = ∫ s, inner ℝ (K s • g s) (∫ t, K t • g t ∂μ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => integral_inner hKg _)
      _ = ∫ s, inner ℝ (∫ t, K t • g t ∂μ) (K s • g s) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => real_inner_comm _ _)
      _ = inner ℝ (∫ s, K s • g s ∂μ) (∫ s, K s • g s ∂μ) := integral_inner hKg _
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hint] at hsum
  exact hsum.mul_left (1/2:ℝ)

lemma nonnegative_coordinate_energy_zero {ι : Type*} {E : ι → ℝ}
    (hs : HasSum E 0) (hE : ∀ i, 0 ≤ E i) (i : ι) : E i = 0 := by
  apply le_antisymm _ (hE i)
  simpa only [hs.tsum_eq] using hs.summable.le_tsum i (fun j _ => hE j)

end StrictHotSpots.HilbertMultipliers
end
end HilbertMultiplierSum

section HilbertKernelCoordinates

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryN_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ fullBoundaryN hC hν s t := by
  rw [fullBoundaryN_eq]
  exact add_nonneg (by unfold boundaryInteraction DiskFormula.boundaryInteraction; positivity) (fullBoundaryR_nonneg hC hν hT s t)

lemma boundary_pair_ne : ∀ᵐ z : Boundary × Boundary ∂boundaryMeasure.prod boundaryMeasure, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet).mpr
  exact Eventually.of_forall fun s => (boundaryMeasure.ae_ne s).mono fun _ h => h.symm


lemma full_embedding_identity {H : Type*} [NormedAddCommGroup H] (p : disk)
    (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
    (hb : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t) :
    ∀ᵐ z : Boundary × Boundary ∂boundaryMeasure.prod boundaryMeasure,
      fullBoundaryN hC hν z.1 z.2 * ‖b z.1-b z.2‖^2 =
        fullBoundaryK hC hν p z.1 * fullBoundaryK hC hν p z.2 := by
  filter_upwards [boundary_pair_ne] with z hz
  rw [hb,fullDistanceKernel,ite_eq_right hz]
  exact mul_div_cancel₀ _ (fullBoundaryN_pos hC hν hT _ _ hz).ne'


theorem full_embedding_coordinate_sum {H E ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Countable ι] (e : HilbertBasis ι ℝ H)
    (p : disk) (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
    (hb : Continuous b) (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t)
    {g : Boundary → E} (hg : Continuous g) :
    HasSum (fun i => (1/2:ℝ)*∫ z : Boundary × Boundary,
      fullBoundaryN hC hν z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 *
        inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)
      ((1/2:ℝ)*‖∫ s, fullBoundaryK hC hν p s • g s ∂boundaryMeasure‖^2) := by
  have hidentity := full_embedding_identity hC hν p hT hid
  obtain ⟨B,hB,hBK⟩ := fullBoundaryK_bounded hC hν p
  obtain ⟨M,hM,hMg⟩ := boundary_continuous_bound hg
  have hKg : Integrable (fun s => fullBoundaryK hC hν p s • g s) boundaryMeasure := by
    apply Integrable.of_bound ((fullBoundaryK_measurable hC hν p).aestronglyMeasurable.smul
      hg.aestronglyMeasurable) (B*M)
    exact Eventually.of_forall fun s => by
      change ‖fullBoundaryK hC hν p s • g s‖ ≤ B*M
      rw [norm_smul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
      exact mul_le_mul (hBK s) (hMg s) (norm_nonneg _) hB
  have hKn : Integrable (fun s => fullBoundaryK hC hν p s * ‖g s‖) boundaryMeasure := by
    apply hKg.norm.congr
    exact Eventually.of_forall fun s => by
      change ‖fullBoundaryK hC hν p s • g s‖ = _
      rw [norm_smul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
  apply HilbertMultipliers.coordinate_energy_sum boundaryMeasure e (fullBoundaryN hC hν)
    (fullBoundaryK hC hν p) b g (fullBoundaryN_nonneg hC hν hT) hidentity hKg
  · apply (hKn.mul_prod hKn).congr
    filter_upwards [hidentity] with z hz
    rw [hz]
    ring
  · intro i
    exact ((fullBoundaryN_measurable hC hν).mul
      ((continuous_const.inner ((hb.comp continuous_fst).sub (hb.comp continuous_snd))).measurable.pow_const 2)).mul
        ((hg.comp continuous_fst).inner (hg.comp continuous_snd)).measurable |>.aestronglyMeasurable

end StrictHotSpots.PlaneGreen
end
end HilbertKernelCoordinates

section OriginalGradientVector

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)
lemma boundary_K_vector_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : disk) (hT : ‖weightedIntegralOperator hC hν‖ < 1) {g : Boundary → E}
    (hg : Continuous g) : Integrable (fun s => fullBoundaryK hC hν p s • g s) boundaryMeasure := by
  obtain ⟨B,hB,hBK⟩ := fullBoundaryK_bounded hC hν p
  obtain ⟨M,_,hMg⟩ := boundary_continuous_bound hg
  apply Integrable.of_bound ((fullBoundaryK_measurable hC hν p).aestronglyMeasurable.smul
    hg.aestronglyMeasurable) (B*M)
  exact Eventually.of_forall fun s => by
    change ‖fullBoundaryK hC hν p s • g s‖ ≤ B*M
    rw [norm_smul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
    exact mul_le_mul (hBK s) (hMg s) (norm_nonneg _) hB
end StrictHotSpots.PlaneGreen
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
lemma boundary_gradient_integral_zero (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) (hz : gradient u (c.F p) = 0) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (∫ s, fullBoundaryK c.densityBound_ne_top
      (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s •
      closedGradient Ω u (c.F s) ∂boundaryMeasure) = 0 := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hμ := firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne
  have hi := boundary_K_vector_integrable c.densityBound_ne_top (c.density_bound hμ.le) p
    (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ) (c.closedGradient_trace_continuous hΩ hu)
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hi
  intro e
  calc
    _ = ∫ s, fullBoundaryK c.densityBound_ne_top (c.density_bound hμ.le) p s *
        inner ℝ (closedGradient Ω u (c.F s)) e ∂boundaryMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by simp only [real_inner_smul_right,real_inner_comm]
    _ = inner ℝ (gradient u (c.F p)) e := (c.gradient_K_representation hΩ hu hne p e).symm
    _ = 0 := by rw [hz,inner_zero_left]
end StrictHotSpots.Conformal.ClosedDiskChart
end
end OriginalGradientVector


end OAI
