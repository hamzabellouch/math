import OAI.Dynamics.TriangleBilliards.FourierTails

namespace OAI

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
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

/-- Local transport commutation with a nonzero generator, obtained from
unitary skew-adjointness and actual kernel adjoint identities. -/
lemma smoothing_direction_pairing (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f p g : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hpm : StronglyMeasurable p) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hg : MemLp g 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) =
      (∫ z, reflectedSmoothing Q ε p z * conj (g z) ∂doubleMeasure Q) := by
  have h := reflectedSmoothingGradient_adjoint Q hε
    (V := fun c => (c.1 : ℂ)) (show Continuous (fun c : DirectionParity => (c.1 : ℂ)) from
      continuous_subtype_val.comp continuous_fst).stronglyMeasurable
    (fun c => (Circle.norm_coe _).le) (fun i c => rfl) hfm hgm hf hg
  have hgen := reflectedSmoothing_supported_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (geodesicHilbertFlow Q).generator_skew hgen hfp
  rw [h, reflectedSmoothing_adjoint Q hε hpm hgm hp hg,
    integral_pairing_toLp hf (reflectedSmoothing_direction_memLp Q hε hgm hg),
    integral_pairing_toLp hp (reflectedSmoothing_memLp Q hε hgm hg)]
  linear_combination -hsk

lemma smoothing_direction_local (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) = reflectedSmoothing Q ε p z := by
  let D : DoublePhase → ℂ := fun z =>
    reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) - reflectedSmoothing Q ε p z
  let E : Set DoublePhase := {z | A ≤ Q.clearance z.1.1}
  let g : DoublePhase → ℂ := E.indicator D
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp (measurable_fst.fst))
  have hDm : StronglyMeasurable D := (reflectedSmoothing_direction_stronglyMeasurable Q ε hfm).sub
    (reflectedSmoothing_stronglyMeasurable Q ε hpm)
  have hDp : MemLp D 2 (doubleMeasure Q) := (reflectedSmoothing_direction_memLp Q hε hfm hf).sub
    (reflectedSmoothing_memLp Q hε hpm hp)
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hJ₀ : 0 ≤ J := (norm_nonneg _).trans (hJ ((0,1),0))
  let C := 4 * derivativeMass * H / ε + 4*J
  have hC : 0 ≤ C := by
    have := derivativeMass_nonneg
    dsimp [C]
    positivity
  have hgb : ∀ z, ‖g z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_mem hz]
      exact (norm_sub_le _ _).trans (add_le_add
        (reflectedSmoothing_direction_norm_bound Q hε hH₀ hH z)
        (reflectedSmoothing_norm_bound Q hε hJ₀ hJ z))
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_notMem hz, norm_zero]
      exact hC
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact Set.indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hpair := smoothing_direction_pairing Q hε hR hsmall hA hfm hpm hgm hf hp hgp hfp hgb hgs
  have he : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    have hDz : (∫ z, D z * conj (g z) ∂doubleMeasure Q) = 0 := by
      simp only [D, sub_mul]
      calc
        _ = (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) -
            (∫ z, reflectedSmoothing Q ε p z * conj (g z) ∂doubleMeasure Q) := by
          convert integral_sub ((reflectedSmoothing_direction_memLp Q hε hfm hf).integrable_mul (memLp_conj hgp))
            ((reflectedSmoothing_memLp Q hε hpm hp).integrable_mul (memLp_conj hgp)) using 1
        _ = 0 := sub_eq_zero.mpr hpair
    rw [← hDz]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ E
    · simp only [g, Set.indicator_of_mem hz]
    · simp only [g, Set.indicator_of_notMem hz, map_zero, mul_zero]
  rw [integral_pairing_toLp hgp hgp, inner_self_eq_zero] at he
  have hgz : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [he] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgz] with z hz hza
  apply sub_eq_zero.mp
  change D z = 0
  simpa only [g, Set.indicator_of_mem (show z ∈ E from hza), Pi.zero_apply] using hz

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma reflectedSmoothingGradient_zero_near_tips (Q : Triangle) {ε A : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hs : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase}
    (hz : z.1.1 ∈ Q.table) (hA : Q.clearance z.1.1 + ε < A) :
    reflectedSmoothingGradient Q ε f z = 0 := by
  have he : (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1] fun _ => 0 := by
    have hc : Continuous (fun y => Q.clearance y + ε) := Q.clearance_lipschitz.continuous.add continuous_const
    filter_upwards [isOpen_interior.eventually_mem hz,
      hc.continuousAt.eventually (gt_mem_nhds hA)] with y hy hr
    exact reflectedSmoothing_zero_near_tips Q hε hs hy hr.le
  rw [← (reflectedSmoothing_hasFDerivAt Q hε hm
    (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
    (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1))
    z.1.1).fderiv]
  rw [he.fderiv_eq, fderiv_const_apply]

/-- Global commutation for inputs and their generators with a genuine
vertex margin. The local identity extends by zero, not by a boundary claim. -/
lemma smoothing_direction_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) :
    (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothing Q ε p := by
  have hl := smoothing_direction_local Q hε hR hsmall (le_refl (2*R+ε)) hfm hpm hf hp hfp hH hJ
  filter_upwards [hl,ae_double_position_in_table Q] with z hz htable
  by_cases hc : 2*R+ε ≤ Q.clearance z.1.1
  · exact hz hc
  · have hcs : Q.clearance z.1.1 + ε < A := by linarith
    rw [reflectedSmoothingGradient_zero_near_tips Q hε hfs hfm hH htable hcs,
      zero_apply, reflectedSmoothing_zero_near_tips Q hε hps htable hcs.le]

lemma supportedSmoothing_generator_commutes (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) :
    (geodesicHilbertFlow Q).HasGenerator
      ((supportedSmoothing_memLp Q hε R hfm hH).toLp _)
      ((supportedSmoothing_memLp Q hε R hpm hJ).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  have hgen := supportedSmoothing_generator Q hε hR hsmall hfm hH
  have he := smoothing_direction_of_supported Q hε hR hsmall hA hfm hpm hf hp hfp hH hJ hfs hps
  have hcongr := (supportedSmoothing_xDerivative_memLp Q hε hRp hfm hH).toLp_congr
    (supportedSmoothing_memLp Q hε R hpm hJ) (by
      filter_upwards [ae_double_position_in_table Q,he] with z hz hh
      rw [supportedSmoothing_derivative_eq_of_supported Q hε hRp hA' hfs hfm hH hz,
        hh, supportedSmoothing_eq_of_supported Q hε hRp hA' hps hz])
  dsimp only at hgen
  rwa [hcongr] at hgen

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate NNReal ContDiff

lemma transverseVelocity_stronglyMeasurable :
    StronglyMeasurable (fun c : DirectionParity => transverseVelocity c.1 c.2) := by
  unfold transverseVelocity
  have hc : Measurable (fun c : DirectionParity => if c.2 = 0 then (Complex.I : ℂ) else -Complex.I) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
  have hv : Continuous (fun c : DirectionParity => (c.1 : ℂ)) := by fun_prop
  exact (hc.mul hv.measurable).stronglyMeasurable

def reflectedSmoothingY (Q : Triangle) (ε : ℝ) (f : DoublePhase → ℂ) : DoublePhase → ℂ :=
  fun z => reflectedSmoothingGradient Q ε f z (transverseVelocity z.1.2 z.2)

lemma reflectedSmoothingY_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothingY Q ε f) 2 (doubleMeasure Q) :=
  gradientApply_memLp (reflectedSmoothingGradient_memLp Q hε hm hf)
    (transverseVelocity_stronglyMeasurable.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
    (fun _z => (norm_transverseVelocity _ _).le)

lemma reflectedSmoothingY_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothingY Q ε f z * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedSmoothingY Q ε g z) ∂doubleMeasure Q) :=
  reflectedSmoothingGradient_adjoint Q hε transverseVelocity_stronglyMeasurable
    (fun c => (norm_transverseVelocity c.1 c.2).le)
    (fun i c => reflect_transverseVelocity Q i c.1 c.2) hfm hgm hf hg

lemma supportedSmoothing_yDerivative_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase} (hz : z.1.1 ∈ Q.table) :
    yDerivative (supportedSmoothing Q ε R f) z = reflectedSmoothingY Q ε f z := by
  have he : (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1]
      (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) := by
    filter_upwards [isOpen_interior.eventually_mem hz] with y hy
    exact supportedSmoothing_eq_of_supported Q hε hR hA hf hy
  change fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) z.1.1 _ = _
  rw [he.fderiv_eq]
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (transverseVelocity z.1.2 z.2))
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv

lemma supportedSmoothing_transverse_generator (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (hf : MemLp f 2 (doubleMeasure Q)) (hs : SpatiallyZero Q A f) :
    (transverseHilbertFlow Q).HasGenerator
      ((supportedSmoothing_memLp Q hε R hm hH).toLp _)
      ((reflectedSmoothingY_memLp Q hε hm hf).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hm hH
  have hd := fun v b => (supportedSmoothing_contDiff Q hε R hm hH v b).differentiable (by simp)
  have hy := yDerivative_memLp_of_gradient_bound Q
    (supportedSmoothing_stronglyMeasurable Q ε R hm).measurable hd hC
  have hgen := seam_transverse_generator (supportedSmoothing_seam Q hε hR hsmall f) hd hC
    (supportedSmoothing_memLp Q hε R hm hH) hy
  have he := hy.toLp_congr (reflectedSmoothingY_memLp Q hε hm hf) (by
    filter_upwards [ae_double_position_in_table Q] with z hz
    exact supportedSmoothing_yDerivative_eq_of_supported Q hε hRp hA hs hm hH hz)
  rwa [he] at hgen

lemma seam_mixed_generators {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {D : ℝ≥0}
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    ∃ c : DoubleL2 Q,
      (geodesicHilbertFlow Q).HasGenerator (hy.toLp _) c ∧
      (transverseHilbertFlow Q).HasGenerator (hx.toLp _) c := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hx' := fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)
  have hy' := fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)
  have hX := xDerivative_fderiv_bound hd hD
  have hY := yDerivative_fderiv_bound hd hD
  have hxy := xDerivative_memLp_of_gradient_bound Q (yDerivative_measurable hm hd') hy' hY
  have hyx := yDerivative_memLp_of_gradient_bound Q (xDerivative_measurable hm hd') hx' hX
  have he := hxy.toLp_congr hyx (Eventually.of_forall (x_y_commute hd))
  refine ⟨hxy.toLp _,seam_geodesic_generator (hs.yDerivative hd') hy' hY hy hxy,?_⟩
  rw [he]
  exact seam_transverse_generator (hs.xDerivative hd') hx' hX hx hyx

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate NNReal ContDiff

/-- The segment pairing is obtained on the actual compactly supported
mollifier domain. No commutation on a rough tail is asserted. -/
lemma clearance_smoothing_pairing (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p)
    {U B : DoubleL2 Q} (hUB : (geodesicHilbertFlow Q).HasGenerator U B) :
    inner ℂ B ((reflectedSmoothingY_memLp Q hε hfm hf).toLp _) =
      inner ℂ ((reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _) (hp.toLp p) := by
  let w := supportedSmoothing Q ε R f
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  have hd := supportedSmoothing_contDiff Q hε R hfm hH
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hfm hH
  obtain ⟨D,hD⟩ := supportedSmoothing_second_bound Q hε hRp hfm hH
  have hm := (supportedSmoothing_stronglyMeasurable Q ε R hfm).measurable
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hx := xDerivative_memLp_of_gradient_bound Q hm hd' hC
  have hy := yDerivative_memLp_of_gradient_bound Q hm hd' hC
  have hw := supportedSmoothing_memLp Q hε R hfm hH
  have hpw := supportedSmoothing_memLp Q hε R hpm hJ
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  have hxg := seam_geodesic_generator hs hd' hC hw hx
  have hyg := seam_transverse_generator hs hd' hC hw hy
  have hxg' := supportedSmoothing_generator_commutes Q hε hR hsmall hA
    hfm hpm hf hp hfp hH hJ hfs hps
  have hex := (geodesicHilbertFlow Q).generator_unique hxg hxg'
  have hyg' := supportedSmoothing_transverse_generator Q hε hR hsmall hA'
    hfm hH hf hfs
  have hey := (transverseHilbertFlow Q).generator_unique hyg hyg'
  obtain ⟨c,hcX,hcY⟩ := seam_mixed_generators hs hm hd hD hx hy
  rw [hex] at hcY
  have hpg := supportedSmoothing_transverse_generator Q hε hR hsmall hA'
    hpm hJ hp hps
  have hec := (transverseHilbertFlow Q).generator_unique hcY hpg
  rw [hey,hec] at hcX
  have hskew := (geodesicHilbertFlow Q).generator_skew hUB hcX
  have hadj := reflectedSmoothingY_adjoint Q hε hpm (Lp.stronglyMeasurable U) hp (Lp.memLp U)
  rw [integral_pairing_toLp (reflectedSmoothingY_memLp Q hε hpm hp) (Lp.memLp U),
    integral_pairing_toLp hp (reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)),
    Lp.toLp_coeFn U (Lp.memLp U)] at hadj
  rw [hadj] at hskew
  exact eq_of_sub_eq_zero (by linear_combination hskew)

end TriangularBilliards

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
