import OAI.Dynamics.TriangleBilliards.ClearanceAverages

namespace OAI

universe uE

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
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction ComplexConjugate
lemma smoothing_lpNorm_tendsto_bounded (Q : Triangle)
    (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ∫ z,
      ‖reflectedSmoothing Q ε f z - f z‖^2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((reflectedSmoothing_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).sub
          f.continuous.stronglyMeasurable).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(5*‖f‖)^2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by
          have h := reflectedSmoothing_norm_bound Q hε (norm_nonneg f) f.norm_coe_le_norm z
          linarith [f.norm_coe_le_norm z])
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [sub_self, norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        (((smoothing_pointwise Q f z hz).sub (tendsto_const_nhds (x := f z))).norm.pow 2)
  simp only [integral_zero] at hi
  have he (ε : ℝ) : lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖reflectedSmoothing Q ε f z - f z‖^2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((reflectedSmoothing_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).sub
        f.continuous.stronglyMeasurable).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma smoothing_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) ≤ 4 * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hf₂.eLpNorm_ne_top)
      (reflectedSmoothing_eLpNorm Q hε hf)

lemma smoothing_lpNorm_tendsto (Q : Triangle)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ/12
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (smoothing_lpNorm_tendsto_bounded Q g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  let Sf := reflectedSmoothing Q ε f
  let Sg := reflectedSmoothing Q ε g
  have hfm := reflectedSmoothing_memLp Q hε hf hf₂
  have hgm := reflectedSmoothing_memLp Q hε g.continuous.stronglyMeasurable hg₂
  have hdm := reflectedSmoothing_memLp Q hε
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have hae : Sf - Sg =ᵐ[doubleMeasure Q] reflectedSmoothing Q ε (f-(g : DoublePhase → ℂ)) :=
    (smoothing_sub_ae Q hε (hf₂.integrable (by norm_num))
      (hg₂.integrable (by norm_num))).symm
  have hb : lpNorm (Sf-Sg) 2 (doubleMeasure Q) ≤ 4*η := by
    rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
      hdm.aestronglyMeasurable hae]
    exact (smoothing_lpNorm_bound Q hε
      (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).trans (by gcongr)
  have hn : lpNorm (Sf-f) 2 (doubleMeasure Q) ≤
      lpNorm (Sf-Sg) 2 (doubleMeasure Q) + lpNorm (Sg-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) +
        lpNorm (f-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) := by
    have heq : Sf-f = ((Sf-Sg)+(Sg-(g : DoublePhase → ℂ)))-(f-(g : DoublePhase → ℂ)) := by ext z; simp only [Pi.sub_apply, Pi.add_apply]; abel
    rw [heq]
    apply (lpNorm_sub_le ((hfm.sub hgm).add (hgm.sub hg₂)) (by norm_num)).trans
    exact add_le_add (lpNorm_add_le (hfm.sub hgm) (by norm_num)) le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg] at he ⊢
  change lpNorm (Sf - f) 2 (doubleMeasure Q) < δ
  change lpNorm (Sg - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) < δ/2 at he
  dsimp [η] at hsmall hb
  linarith

end TriangularBilliards

namespace TriangularBilliards.Analytic
open Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma WeaklyTendsto.inner_right {u : ℕ → E} {v : E}
    (h : WeaklyTendsto u atTop v) (w : E) :
    Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)) := by
  have hr := h (Complex.reCLM.comp ((innerSL ℂ w).restrictScalars ℝ))
  have hi := h (Complex.imCLM.comp ((innerSL ℂ w).restrictScalars ℝ))
  have hh := (Complex.continuous_ofReal.tendsto _ |>.comp hr).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp hi).mul_const Complex.I)
  change Tendsto (fun n => ((inner ℂ w (u n)).re : ℂ) + ((inner ℂ w (u n)).im : ℂ)*Complex.I)
    atTop (𝓝 (((inner ℂ w v).re : ℂ) + ((inner ℂ w v).im : ℂ)*Complex.I)) at hh
  simpa only [Complex.re_add_im] using hh

end TriangularBilliards.Analytic

namespace TriangularBilliards
open Analysis Analytic Filter
open scoped Topology ComplexConjugate

noncomputable def smoothingLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (u : DoubleL2 Q) : DoubleL2 Q :=
  (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable u) (Lp.memLp u)).toLp _

lemma smoothingLp_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (u v : DoubleL2 Q) :
    inner ℂ u (smoothingLp Q hε v) = inner ℂ (smoothingLp Q hε u) v := by
  have h := reflectedSmoothing_adjoint Q hε (Lp.stronglyMeasurable v)
    (Lp.stronglyMeasurable u) (Lp.memLp v) (Lp.memLp u)
  rw [integral_pairing_toLp (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable v) (Lp.memLp v)) (Lp.memLp u),
    integral_pairing_toLp (Lp.memLp v) (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable u) (Lp.memLp u)),
    Lp.toLp_coeFn u (Lp.memLp u), Lp.toLp_coeFn v (Lp.memLp v)] at h
  exact h

lemma smoothingLp_tendsto (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0)) (u : DoubleL2 Q) :
    Tendsto (fun n => smoothingLp Q (hε n) u) atTop (𝓝 u) := by
  have he' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hε⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert (smoothing_lpNorm_tendsto Q (Lp.stronglyMeasurable u) (Lp.memLp u)).comp he' using 1
  ext n
  have hm := reflectedSmoothing_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)
  rw [show smoothingLp Q (hε n) u - u = (hm.sub (Lp.memLp u)).toLp
      (reflectedSmoothing Q (ε n) u - (u : DoublePhase → ℂ)) by
    rw [MemLp.toLp_sub _ (Lp.memLp u), Lp.toLp_coeFn]; rfl]
  rw [Lp.norm_toLp, toReal_eLpNorm]
  rfl

lemma smoothing_variable_pairing (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0))
    {u : ℕ → DoubleL2 Q} {H : ℝ} (hu : ∀ n, ‖u n‖ ≤ H) (v : DoubleL2 Q) :
    Tendsto (fun n => inner ℂ v (smoothingLp Q (hε n) (u n) - u n)) atTop (𝓝 0) := by
  have hv := (smoothingLp_tendsto Q hε he v).sub_const v
  have hb : Tendsto (fun n => ‖smoothingLp Q (hε n) v - v‖ * H) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_mul] using hv.norm.mul_const H
  apply squeeze_zero_norm _ hb
  intro n
  rw [inner_sub_right,smoothingLp_adjoint,← inner_sub_left]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _))

end TriangularBilliards

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma smoothing_toLp_eq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (reflectedSmoothing_memLp Q hε hfm hf).toLp _ = smoothingLp Q hε (hf.toLp f) := by
  apply ext_inner_left ℂ
  intro v
  have hadj := reflectedSmoothing_adjoint Q hε hfm (Lp.stronglyMeasurable v) hf (Lp.memLp v)
  rw [integral_pairing_toLp (reflectedSmoothing_memLp Q hε hfm hf) (Lp.memLp v),
    integral_pairing_toLp hf (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable v) (Lp.memLp v)),
    Lp.toLp_coeFn v (Lp.memLp v)] at hadj
  exact hadj.trans (smoothingLp_adjoint Q hε v (hf.toLp f)).symm

/-- One actual long-clearance-segment approximation, with all bounds and
its relevant Fourier derivative pairing. -/
lemma exists_clearance_data (Q : Triangle) {L ε R T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H)
    (hR : Q.safetyFactor*ε < R) (hsmall : 2*R*Q.coordinateBound < 1)
    (hL : 2*R+2*ε ≤ L*ε)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {U B : DoubleL2 Q}
    (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    ∃ g w p a b : DoubleL2 Q,
      (∀ᵐ z ∂doubleMeasure Q, ‖g z‖ ≤ H) ∧
      ‖g-f‖ ≤ H*(doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal^(1/2:ℝ) ∧
      (geodesicHilbertFlow Q).HasGenerator g p ∧ ‖p‖ ≤ 2*H/T ∧
      w = smoothingLp Q hε g ∧ ‖w‖ ≤ 4*H ∧
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j w) a b ∧
      ‖a‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖b‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖inner ℂ B b‖ ≤ 4*‖B‖*H/T + H/T *
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ := by
  let g := clearanceAverage Q L ε T f
  have hgb := clearanceAverage_bounded Q (L:=L) (ε:=ε) hT hH hf
  have hgs := clearanceAverage_zero Q (L:=L) hT hε f
  obtain ⟨p,hgp,hpb,hps⟩ := clearanceAverage_generator_supported Q (L:=L) hε hT hH hf
  obtain ⟨g₀,hgm,hg₀b,hg₀s,hg₀⟩ := exists_bounded_supported_representative Q hH hgb hgs
  obtain ⟨p₀,hpm,hp₀b,hp₀s,hp₀⟩ := exists_bounded_supported_representative Q
    (by positivity : 0 ≤ 2*H/T) hpb hps
  have hgmem := (Lp.memLp g).ae_eq hg₀.symm
  have hpmem := (Lp.memLp p).ae_eq hp₀.symm
  have hgeq : hgmem.toLp g₀ = g := by
    apply Lp.ext
    exact hgmem.coeFn_toLp.trans hg₀
  have hpeq : hpmem.toLp p₀ = p := by
    apply Lp.ext
    exact hpmem.coeFn_toLp.trans hp₀
  have hgp₀ : (geodesicHilbertFlow Q).HasGenerator (hgmem.toLp g₀) (hpmem.toLp p₀) := by
    rw [hgeq,hpeq]; exact hgp
  obtain ⟨a,b,hcr,ha,hb,hpair⟩ := supported_source_CR Q hε hT hH hR hsmall hL
    hgm hpm hgmem hpmem hgp₀ hg₀b hp₀b hg₀s hp₀s j hUB hB
  let hw := supportedSmoothing_memLp Q hε R hgm hg₀b
  let w := hw.toLp (supportedSmoothing Q ε R g₀)
  refine ⟨g,w,p,a,b,hgb,(clearanceAverage_estimates Q hT hH hf hinv).1,hgp,?_,?_,?_,hcr,ha,hb,hpair⟩
  · exact doubleL2_norm_le_of_ae_bound Q (by positivity) hpb
  · have he := hw.toLp_congr (reflectedSmoothing_memLp Q hε hgm hgmem) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_eq_of_supported Q hε
        ((mul_pos Q.safetyFactor_pos hε).trans hR) (by linarith) hg₀s hz)
    change w = _ at he
    rw [he,smoothing_toLp_eq Q hε hgm hgmem,hgeq]
  · apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [hw.coeFn_toLp] with z hz
    rw [hz]
    exact supportedSmoothing_norm_bound Q hε R hH hg₀b z

end TriangularBilliards

namespace TriangularBilliards.Analytic
open Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma weaklyTendsto_of_inner {u : ℕ → E} {v : E}
    (h : ∀ w, Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) :
    WeaklyTendsto u atTop v := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  intro L
  let w := (InnerProductSpace.toDual ℝ E).symm L
  have hw : ∀ x, (inner ℂ w x).re = L x := by
    intro x
    change (InnerProductSpace.toDual ℝ E) w x = L x
    rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [Function.comp_def,hw] using Complex.continuous_re.tendsto _ |>.comp (h w)

end TriangularBilliards.Analytic

end
end
end
end
end
end
end
end
end
end

end OAI
