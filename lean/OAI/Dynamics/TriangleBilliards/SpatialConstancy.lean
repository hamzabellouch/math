import OAI.Dynamics.TriangleBilliards.SpatialRigidity

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
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma bounded_invariant_transverse (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f) :
    (transverseHilbertFlow Q).HasGenerator f 0 := by
  apply ((transverseHilbertFlow Q).hasGenerator_zero_iff f).mpr
  intro t
  have hj (j : ℤ) : (transverseHilbertFlow Q).act t ((angularCircleAction Q).projection j f) =
      (angularCircleAction Q).projection j f := by
    have hh := (bounded_invariant_rigidity Q hH hf hinv j).generators.2
    simp only [sub_self,smul_zero] at hh
    exact hh.invariant t
  calc
    _ = (transverseHilbertFlow Q).act t (∑' j : ℤ, (angularCircleAction Q).projection j f) := by
      rw [(angularCircleAction Q).tsum_projection]
    _ = ∑' j : ℤ, (transverseHilbertFlow Q).act t ((angularCircleAction Q).projection j f) :=
      ((transverseHilbertFlow Q).act t).toContinuousLinearMap.map_tsum
        ((angularCircleAction Q).summable_projection f)
    _ = _ := by simp only [hj,(angularCircleAction Q).tsum_projection]

lemma transverse_invariant_smoothing_pairing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q))
    (hfi : (transverseHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingY Q ε f z * conj (g z) ∂doubleMeasure Q) = 0 := by
  have hgen := supportedSmoothing_transverse_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (transverseHilbertFlow Q).generator_skew hfi hgen
  simp only [inner_zero_left,add_zero] at hsk
  have hh := reflectedSmoothingY_adjoint Q hε hfm hgm hf hg
  rw [hh,integral_pairing_toLp hf (reflectedSmoothingY_memLp Q hε hgm hg)]
  rw [inner_eq_zero_symm.mpr hsk,neg_zero]

lemma transverse_invariant_smoothing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (transverseHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 → reflectedSmoothingY Q ε f z = 0 := by
  let D := reflectedSmoothingY Q ε f
  let E := {z : DoublePhase | A ≤ Q.clearance z.1.1}
  have hDp := reflectedSmoothingY_memLp Q hε hfm hf
  have hDm := isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((reflectedSmoothingGradient_stronglyMeasurable Q ε hfm).prodMk
      (transverseVelocity_stronglyMeasurable.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp measurable_fst.fst)
  let g := E.indicator D
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hgb : ∀ z, ‖g z‖ ≤ 4*derivativeMass*H/ε := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [indicator_of_mem hz]
      exact reflectedSmoothingY_norm_bound Q hε hH₀ hH z
    · change ‖E.indicator D z‖ ≤ _
      rw [indicator_of_notMem hz,norm_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) hH₀) hε.le
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hp := transverse_invariant_smoothing_pairing_zero Q hε hR hsmall hA hfm hgm hf hgp hfi hgb hgs
  have hi : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    rw [← hp]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ E
    · simp only [g,indicator_of_mem hz,D]
    · simp only [g,indicator_of_notMem hz,map_zero,mul_zero]
  rw [integral_pairing_toLp hgp hgp,inner_self_eq_zero] at hi
  have hgzero : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [hi] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgzero] with z hz hza
  simpa only [g,indicator_of_mem (show z ∈ E from hza),Pi.zero_apply] using hz

lemma realLinear_zero_of_velocity_transverse (L : ℂ →L[ℝ] ℂ) (v : Circle) (b : ZMod 2)
    (hx : L (v : ℂ)=0) (hy : L (transverseVelocity v b)=0) : L=0 := by
  have hi : L (Complex.I*(v:ℂ))=0 := by
    by_cases hb : b=0
    · simpa only [transverseVelocity,hb,ite_true] using hy
    · simpa only [transverseVelocity,hb,ite_false,neg_mul,map_neg,neg_eq_zero] using hy
  ext z
  have hv : (v:ℂ) ≠ 0 := Circle.coe_ne_zero v
  have hz : z = (z/(v:ℂ)).re • (v:ℂ) + (z/(v:ℂ)).im • (Complex.I*(v:ℂ)) := by
    rw [Complex.real_smul,Complex.real_smul]
    calc
      _ = (z/(v:ℂ))*(v:ℂ) := (div_mul_cancel₀ z hv).symm
      _ = _ := by
        conv_lhs => rw [← Complex.re_add_im (z/(v:ℂ))]
        simp only [div_eq_mul_inv]
        ring
  rw [hz,map_add,map_smul,map_smul,hx,hi,smul_zero,smul_zero,add_zero]
  rfl

lemma invariant_smoothing_gradient_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) z.1.1 = 0 := by
  have hb : ∀ᵐ z ∂doubleMeasure Q, ‖(hf.toLp f) z‖ ≤ H := by
    filter_upwards [hf.coeFn_toLp] with z hz
    simpa only [hz] using hH z
  have hfy := bounded_invariant_transverse Q ((norm_nonneg _).trans (hH ((0,1),0))) hb hfx.invariant
  filter_upwards [invariant_smoothing_direction_zero Q hε hR hsmall hA hfm hf hfx hH,
    transverse_invariant_smoothing_zero Q hε hR hsmall hA hfm hf hfy hH] with z hx hy ha
  have he := (reflectedSmoothing_hasFDerivAt Q hε hfm
    (bounded_spatialSlice_integrable Q hfm hH z.1.2 z.2)
    (fun i => bounded_spatialSlice_integrable Q hfm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv
  rw [he]
  exact realLinear_zero_of_velocity_transverse _ z.1.2 z.2 (hx ha) (hy ha)

end TriangularBilliards

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

lemma double_ae_slices (Q : Triangle) {p : DoublePhase → Prop}
    (hp : ∀ᵐ z ∂doubleMeasure Q, p z) :
    ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), p ((x,c.1),c.2) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have ha := (measurePreserving_prodAssoc μ angularMeasure parityMeasure).symm MeasurableEquiv.prodAssoc
  exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ := angularMeasure.prod parityMeasure) (ν := μ)).quasiMeasurePreserving.ae
      (ha.quasiMeasurePreserving.ae hp))

lemma double_ae_of_slices (Q : Triangle) {f g : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hp : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), f ((x,c.1),c.2)=g ((x,c.1),c.2)) :
    f =ᵐ[doubleMeasure Q] g := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hm : MeasurableSet {p : DirectionParity × ℂ | f ((p.2,p.1.1),p.1.2)=g ((p.2,p.1.1),p.1.2)} :=
    measurableSet_eq_fun (hfm.measurable.comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd))
      (hgm.measurable.comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd))
  have hh := (Measure.ae_prod_iff_ae_ae hm).mpr hp
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hh
  exact (measurePreserving_prodAssoc μ angularMeasure parityMeasure).quasiMeasurePreserving.ae hs

lemma smoothing_gradient_zero_on_slice (Q : Triangle) {ε A : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (c : DirectionParity)
    (hD : ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table),
      A ≤ Q.clearance x → fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x=0) :
    ∀ x ∈ Q.table, A < Q.clearance x →
      fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x=0 := by
  let U := Q.table ∩ {x | A < Q.clearance x}
  have hU : IsOpen U := Q.isOpen_table.inter (isOpen_lt continuous_const Q.clearance_lipschitz.continuous)
  have hd := (Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hD
  have he : (fun x => fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x)
      =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hd,
      ae_restrict_mem hU.measurableSet] with x hx hu
    exact hx hu.2.le
  have hsm := reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
    (fun i => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q i c.1) (c.2+1))
  exact fun x hx ha => Measure.eqOn_open_of_ae_eq he hU
    (hsm.continuous_fderiv (by simp)).continuousOn continuousOn_const ⟨hx,ha⟩

end TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

lemma eventual_equal_of_vanishing_gradient {U : Set ℂ} (hU : Convex ℝ U)
    {d : ℂ → ℝ} (hd : Continuous d) (hpos : ∀ x ∈ U, 0 < d x)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, Differentiable ℝ (F n))
    (hD : ∀ n x, x ∈ U → a n < d x → fderiv ℝ (F n) x = 0)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ∀ᶠ n in atTop, F n x = F n y := by
  have hs : segment ℝ x y ⊆ U := hU.segment_subset hx hy
  have hscompact : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨z,hz,hm⟩ := hscompact.exists_isMinOn ⟨x,left_mem_segment ℝ x y⟩ hd.continuousOn
  have hp := hpos z (hs hz)
  filter_upwards [ha.eventually (gt_mem_nhds hp)] with n hn
  have hdz : ∀ w ∈ segment ℝ x y, fderiv ℝ (F n) w=0 := by
    intro w hw
    exact hD n w (hs hw) (hn.trans_le (hm hw))
  have hl := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F n) (f' := fun _ => (0 : ℂ →L[ℝ] ℂ)) (C := (0:ℝ))
    (fun w hw => (hdz w hw ▸ (hF n w).hasFDerivAt).hasFDerivWithinAt)
    (fun _ _ => by simp) (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : F n y = F n x := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hl))
  exact he.symm

lemma ae_constant_of_eventual_equal {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {U : Set ℂ} (hU : ∀ᵐ x ∂μ, x ∈ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (he : ∀ x ∈ U, ∀ y ∈ U, ∀ᶠ n in atTop, F n x = F n y) :
    f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  obtain ⟨y,hy,hcy⟩ := (hU.and hc).exists
  have hfe : f =ᵐ[μ] fun _ => f y := by
    filter_upwards [hU,hc] with x hx hcx
    apply tendsto_nhds_unique hcx
    apply hcy.congr'
    filter_upwards [he x hx y hy] with n hn
    exact hn.symm
  have hi : (∫ x, f x ∂μ) = f y := by
    simp only [integral_congr_ae hfe,integral_const,probReal_univ,one_smul]
  simpa only [hi] using hfe

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

/-- The actual bounded invariant is independent of the spatial position on each
of the two triangle sheets, almost everywhere in direction and sheet. -/
theorem bounded_invariant_spatial_constancy (Q : Triangle)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) :
    ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      (fun x => f ((x,c.1),c.2)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table]
        (fun _ => ∫ x, f ((x,c.1),c.2) ∂((volume Q.table)⁻¹ • volume.restrict Q.table)) := by
  let K := Q.safetyFactor+1
  have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    simpa using hc.continuousAt.eventually (gt_mem_nhds (by simp only [mul_zero,zero_mul]; norm_num))
  obtain ⟨δ,hδ,hδb⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,he⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 := hδb
    (by simpa only [Real.dist_eq,sub_zero,abs_of_pos (hpos n)] using (hε n).2)
  have hR (n : ℕ) : Q.safetyFactor*ε n < K*ε n := by dsimp [K]; nlinarith [hpos n]
  let A : ℕ → ℝ := fun n => (2*K+1)*ε n
  have hA (n : ℕ) : 2*(K*ε n)+ε n ≤ A n := by dsimp [A]; ring_nf; rfl
  have hder (n : ℕ) := double_ae_slices Q (invariant_smoothing_gradient_zero Q (hpos n)
    (hR n) (hsmall n) (hA n) hfm hf hfx hb)
  have hlim := smoothingLp_tendsto Q hpos he (hf.toLp f)
  obtain ⟨φ,hφ,hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hpoint' : ∀ᵐ z ∂doubleMeasure Q,
      Tendsto (fun n => reflectedSmoothing Q (ε (φ n)) f z) atTop (𝓝 (f z)) := by
    have hcoe (n : ℕ) : ∀ᵐ z ∂doubleMeasure Q,
        (smoothingLp Q (hpos (φ n)) (hf.toLp f)) z = reflectedSmoothing Q (ε (φ n)) f z := by
      rw [← smoothing_toLp_eq Q (hpos (φ n)) hfm hf]
      exact (reflectedSmoothing_memLp Q (hpos (φ n)) hfm hf).coeFn_toLp
    filter_upwards [hpoint,hf.coeFn_toLp,ae_all_iff.mpr hcoe] with z hz hfz hsz
    simpa only [hfz,hsz] using hz
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have hμU : ∀ᵐ x ∂μ, x ∈ Q.table := Measure.ae_smul_measure (ae_restrict_mem Q.measurableSet_table) _
  filter_upwards [double_ae_slices Q hpoint',ae_all_iff.mpr hder] with c hc hdc
  apply ae_constant_of_eventual_equal hμU hc
  intro x hx y hy
  apply eventual_equal_of_vanishing_gradient (convex_convexHull ℝ (range Q.vertex)).interior
    Q.clearance_lipschitz.continuous (fun z hz => Q.clearance_pos_of_mem_table hz)
    (a := fun n => A (φ n)) (by simpa only [A,mul_zero,Function.comp_def] using (he.comp hφ.tendsto_atTop).const_mul (2*K+1))
    (fun n => (reflectedSmoothing_contDiff Q (hpos (φ n))
      (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
      (fun i => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q i c.1) (c.2+1))).differentiable (by simp))
    (fun n => smoothing_gradient_zero_on_slice Q (hpos (φ n)) hfm hb c (hdc (φ n))) hx hy

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
end

end OAI
