import OAI.Dynamics.TriangleBilliards.SpatialConstancy

namespace OAI

universe uAlpha uBeta

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
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

def spatialMean (Q : Triangle) (f : DoublePhase → ℂ) (c : DirectionParity) : ℂ :=
  ∫ x, f ((x,c.1),c.2) ∂((volume Q.table)⁻¹ • volume.restrict Q.table)

lemma spatialMean_stronglyMeasurable (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (spatialMean Q f) := by
  have h : StronglyMeasurable (Function.uncurry (fun c : DirectionParity => fun x : ℂ => f ((x,c.1),c.2))) :=
    hf.comp_measurable ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd)
  exact h.integral_prod_right

lemma Triangle.clearance_pos_of_mem_side (Q : Triangle) {q : ℂ} {i : Fin 3} (hq : q ∈ Q.side i) :
    0 < Q.clearance q := by
  apply ((finite_range Q.vertex).isClosed.notMem_iff_infDist_pos (range_nonempty _)).mp
  rintro ⟨k,rfl⟩
  obtain ⟨j,hjk,hji⟩ := (by decide : ∀ i k : Fin 3, ∃ j : Fin 3, j≠k ∧ j≠i+2) i k
  have hj : Q.basis.coord j (Q.vertex k)=0 := (Q.basis.coord_apply j k).trans (ite_eq_right hjk)
  exact hji ((Q.side_coord_zero_iff hq j).mp hj)

lemma Triangle.side_mem_hull (Q : Triangle) {q : ℂ} {i : Fin 3} (hq : q ∈ Q.side i) :
    q ∈ convexHull ℝ (range Q.vertex) :=
  (convex_convexHull ℝ (range Q.vertex)).segment_subset
    (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self (i+1)))
      (openSegment_subset_segment ℝ _ _ hq)

lemma directS_eq_const_of_slice (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {v : Circle} {b : ZMod 2} {a : ℂ}
    (hf : (fun y => f ((y,v),b)) =ᵐ[volume.restrict Q.table] (fun _ => a))
    {x : ℂ} (hx : Metric.ball x ε ⊆ Q.table) : directS Q ε f b v x = a := by
  have hi : (∫ y in Q.table, kernel ε (x-y)) = 1 := by
    rw [← integral_indicator Q.measurableSet_table]
    calc
      _ = ∫ y : ℂ, kernel ε (x-y) := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y∈Q.table
        · exact indicator_of_mem hy _
        · rw [indicator_of_notMem hy]
          symm
          by_contra hn
          have hm : x-y ∈ support (kernel ε) := hn
          rw [kernel_support hε,mem_ball_zero_iff] at hm
          apply hy
          apply hx
          simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hm
      _ = 1 := (integral_sub_left_eq_self (fun y : ℂ => kernel ε y) volume x).trans (kernel_integral hε)
  calc
    _ = ∫ y in Q.table, kernel ε (x-y) • a := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    _ = a := by rw [integral_smul_const,hi,one_smul]

lemma reflectedSmoothing_eq_const_of_slice (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {v : Circle} {b : ZMod 2} {a : ℂ}
    (hf : (fun y => f ((y,v),b)) =ᵐ[volume.restrict Q.table] (fun _ => a))
    {x : ℂ} (hx : Metric.ball x ε ⊆ Q.table)
    (hcoord : ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x) :
    reflectedSmoothing Q ε f ((x,v),b) = a := by
  rw [reflectedSmoothing,directS_eq_const_of_slice Q hε hf hx]
  have hz : (∑ j : Fin 3, reflectedS Q j ε f b v x)=0 :=
    Finset.sum_eq_zero (fun j _ => reflectedS_zero_of_coord Q j hε f b v (hcoord j))
  rw [hz,add_zero]

end TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

lemma equal_of_zero_gradient_openSegment {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F)
    {x y : ℂ} (hD : ∀ z ∈ openSegment ℝ x y, fderiv ℝ F z=0) : F x=F y := by
  have hcl := closure_minimal hD (isClosed_eq (hF.continuous_fderiv (by simp)) continuous_const)
  rw [closure_openSegment] at hcl
  have hl := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (f' := fun _ => (0 : ℂ →L[ℝ] ℂ)) (C := (0:ℝ))
    (fun w hw => (hcl hw ▸ (hF.differentiable (by simp) w).hasFDerivAt).hasFDerivWithinAt)
    (fun _ _ => by simp) (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hl))).symm

lemma irrational_arg_of_angle {a b : ℂ} (ha : a≠0) (hb : b≠0)
    (h : Irrational (InnerProductGeometry.angle a b / Real.pi)) :
    Irrational ((conj a*b).arg / Real.pi) := by
  have he : InnerProductGeometry.angle a b = |(conj a*b).arg| := by
    rw [Complex.orientation.angle_eq_abs_oangle_toReal ha hb,Complex.oangle,Complex.arg_coe_angle_toReal_eq_arg]
  rw [he] at h
  rcases le_or_gt 0 (conj a*b).arg with hn|hn
  · simpa only [abs_of_nonneg hn] using h
  · simpa only [abs_of_neg hn,neg_div,irrational_neg_iff] using h

lemma complex_div_conj_eq_exp_double_arg {w : ℂ} (hw : w≠0) :
    w / conj w = Complex.exp (2*(w.arg:ℂ)*Complex.I) := by
  have hn : (‖w‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hconj : conj w = (‖w‖:ℂ)*Complex.exp (-(w.arg:ℂ)*Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I]
    congr 2; ring
  rw [hconj]
  conv_lhs => lhs; rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_div_mul_left _ _ hn,← Complex.exp_sub]
  congr 1
  ring

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

lemma spatialMean_reflection_invariant (Q : Triangle)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (i : Fin 3) :
    spatialMean Q f ∘ directionParityReflection Q i =ᵐ[angularMeasure.prod parityMeasure]
      spatialMean Q f := by
  obtain ⟨x,hx⟩ := Q.table_nonempty
  let q := midpoint ℝ (Q.vertex i) (Q.vertex (i+1))
  have hq : q ∈ Q.side i := midpoint_mem_openSegment _ _
  have hopen : openSegment ℝ x q ⊆ Q.table :=
    (convex_convexHull ℝ (range Q.vertex)).openSegment_interior_self_subset_interior hx (Q.side_mem_hull hq)
  have hpos : ∀ y ∈ segment ℝ x q, 0 < Q.clearance y := by
    intro y hy
    rw [← insert_endpoints_openSegment] at hy
    rcases hy with rfl|rfl|hy
    · exact Q.clearance_pos_of_mem_table hx
    · exact Q.clearance_pos_of_mem_side hq
    · exact Q.clearance_pos_of_mem_table (hopen hy)
  have hscompact : IsCompact (segment ℝ x q) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨y,hy,hmin⟩ := hscompact.exists_isMinOn ⟨x,left_mem_segment ℝ x q⟩
    Q.clearance_lipschitz.continuous.continuousOn
  obtain ⟨r,hr,hrball⟩ := Metric.mem_nhds_iff.mp (Q.isOpen_table.mem_nhds hx)
  let K := Q.safetyFactor+1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hev (a d : ℝ) (hd : 0 < d) : ∀ᶠ ε : ℝ in 𝓝 0, a*ε < d := by
    have hc : Continuous (fun ε : ℝ => a*ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hd))
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0,
      2*(K*ε)*Q.coordinateBound < 1 ∧ (2*K+1)*ε < Q.clearance y ∧ ε<r ∧
        ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x := by
    filter_upwards [hev (2*K*Q.coordinateBound) 1 (by norm_num),
      hev (2*K+1) _ (hpos y hy),hev 1 r hr,
      Filter.eventually_all.mpr (fun j : Fin 3 => hev Q.coordinateBound _ ((Q.table_iff_coords x).mp hx (j+2)))]
      with ε h₁ h₂ h₃ h₄
    exact ⟨by nlinarith,h₂,by simpa using h₃,h₄⟩
  have hnb' : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ 2*(K*ε)*Q.coordinateBound < 1 ∧ (2*K+1)*ε < Q.clearance y ∧ ε<r ∧
        ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x :=
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and (hnb.filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε,hε,hsmall,hsafe,her,hcoord⟩ := hnb'.exists
  let R := K*ε
  let A := (2*K+1)*ε
  have hR : Q.safetyFactor*ε < R := by dsimp [R,K]; nlinarith
  have hA : 2*R+ε ≤ A := by dsimp [R,A]; ring_nf; rfl
  have hseg : ∀ z∈segment ℝ x q, A < Q.clearance z := fun z hz => hsafe.trans_le (hmin hz)
  have hseam : Q.safetyFactor*ε < Q.clearance q := by
    have hh := hseg q (right_mem_segment ℝ x q)
    dsimp [A,K] at hh
    nlinarith [Q.safetyFactor_pos]
  have hball : Metric.ball x ε ⊆ Q.table := (Metric.ball_subset_ball her.le).trans hrball
  have hconst := bounded_invariant_spatial_constancy Q hfm hf hb hfx
  have hD := double_ae_slices Q (invariant_smoothing_gradient_zero Q hε hR hsmall hA hfm hf hfx hb)
  filter_upwards [hconst,hD,(measurePreserving_directionParity Q i).quasiMeasurePreserving.ae hconst,
    (measurePreserving_directionParity Q i).quasiMeasurePreserving.ae hD] with c hc hd hrc hrd
  have he (c : DirectionParity)
      (hc : (fun z => f ((z,c.1),c.2)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table]
        (fun _ => spatialMean Q f c))
      (hd : ∀ᵐ z ∂((volume Q.table)⁻¹ • volume.restrict Q.table), A ≤ Q.clearance z →
        fderiv ℝ (fun w => reflectedSmoothing Q ε f ((w,c.1),c.2)) z=0) :
      reflectedSmoothing Q ε f ((q,c.1),c.2) = spatialMean Q f c := by
    have hsm := reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
      (fun j => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q j c.1) (c.2+1))
    have hdx := smoothing_gradient_zero_on_slice Q hε hfm hb c hd
    have hxy := equal_of_zero_gradient_openSegment hsm (fun z hz => hdx z (hopen hz)
      (hseg z (openSegment_subset_segment ℝ x q hz)))
    rw [← hxy]
    exact reflectedSmoothing_eq_const_of_slice Q hε
      ((Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hc) hball hcoord
  have hs := (reflectedSmoothing_seam_germ Q hq hε hseam f c.2 c.1).self_of_nhds
  rw [wallReflection_fixed_side Q hq] at hs
  change spatialMean Q f (directionParityReflection Q i c) = spatialMean Q f c
  rw [← he _ hrc hrd,← he _ hc hd]
  exact hs

end TriangularBilliards

namespace TriangularBilliards
open scoped ComplexConjugate
lemma reflectedDirection_pair (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q (i+2) (reflectedDirection Q i v) =
      Circle.exp (2 * (conj (Q.vertex (i+1)-Q.vertex i) * (Q.vertex (i+2)-Q.vertex i)).arg) * v := by
  let a := Q.vertex (i+1)-Q.vertex i
  let b := Q.vertex (i+2)-Q.vertex i
  have ha : a ≠ 0 := Q.tangent_ne_zero i
  have hb : b ≠ 0 := sub_ne_zero.mpr (Q.nondegenerate.injective.ne (by omega))
  have he : Q.tangent (i+2) = -b := by
    dsimp [Triangle.tangent,b]
    rw [show i+2+1=i by omega]
    abel
  have hw : conj a*b ≠ 0 := mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr ha) hb
  apply Subtype.ext
  change reflect (Q.tangent (i+2)) (reflect (Q.tangent i) (v:ℂ)) = _
  rw [he]
  change reflect (-b) (reflect a (v:ℂ)) = _
  simp only [reflect,Complex.star_def,map_mul,map_div₀,map_neg,RingHomCompTriple.comp_apply,
    RingHom.id_apply,Circle.coe_mul,Circle.coe_exp,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [← complex_div_conj_eq_exp_double_arg hw]
  simp only [map_mul,Complex.conj_conj]
  field_simp

end TriangularBilliards

namespace TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma angle_irrational_ergodic {a : ℝ} (ha : Irrational (a / Real.pi)) :
    Ergodic (fun x : AddCircle (2*Real.pi) => (2*a : ℝ) + x)
      ((ENNReal.ofReal (2*Real.pi))⁻¹ • volume) := by
  let : IsFiniteMeasure (((ENNReal.ofReal (2*Real.pi))⁻¹) • (volume : Measure (AddCircle (2*Real.pi)))) :=
    Measure.smul_finite volume (ENNReal.inv_ne_top.mpr (by positivity))
  apply ergodic_add_left_of_denseRange_zsmul
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  convert ha using 1
  field_simp

lemma angular_reflections_constant (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    {g : Circle → ℂ} (hg : StronglyMeasurable g)
    (hi : ∀ i : Fin 3, g ∘ reflectedDirection Q i =ᵐ[angularMeasure] g) :
    ∃ a : ℂ, g =ᵐ[angularMeasure] fun _ => a := by
  obtain ⟨i,hiirr⟩ := hQ
  let a := Q.vertex (i+1)-Q.vertex i
  let b := Q.vertex (i+2)-Q.vertex i
  let θ := (conj a*b).arg
  have ha : a≠0 := Q.tangent_ne_zero i
  have hb : b≠0 := sub_ne_zero.mpr (Q.nondegenerate.injective.ne (by omega))
  have hθ : Irrational (θ/Real.pi) := irrational_arg_of_angle ha hb hiirr
  have hinv : (fun v => g (Circle.exp (2*θ)*v)) =ᵐ[angularMeasure] g := by
    filter_upwards [hi i,(measurePreserving_reflectedDirection Q i).quasiMeasurePreserving.ae (hi (i+2))]
      with v hv hrv
    rw [Function.comp_apply,reflectedDirection_pair] at hrv
    exact hrv.trans hv
  let e := AddCircle.homeomorphCircle'
  have hgm : StronglyMeasurable (g ∘ e) := hg.comp_measurable measurePreserving_toCircle.measurable
  have hie : (g ∘ e) ∘ (fun x : AddCircle (2*Real.pi) => (2*θ : ℝ)+x) =ᵐ[angleMeasure] g ∘ e := by
    filter_upwards [measurePreserving_toCircle.quasiMeasurePreserving.ae hinv] with x hx
    have hadd : e (((2*θ : ℝ) : AddCircle (2*Real.pi))+x) =
        Circle.exp (2*θ)*e x :=
      (Real.Angle.toCircle_add (((2*θ : ℝ) : AddCircle (2*Real.pi))) x).trans
        (congrArg (fun z : Circle => z * e x) (Real.Angle.toCircle_coe (2*θ)))
    change g (e (((2*θ : ℝ) : AddCircle (2*Real.pi))+x)) = g (e x)
    rw [hadd]
    exact hx
  obtain ⟨c,hc⟩ := (angle_irrational_ergodic hθ).ae_eq_const_of_ae_eq_comp_ae hgm.aestronglyMeasurable hie
  refine ⟨c,?_⟩
  rw [← measurePreserving_toCircle.map_eq]
  exact (ae_map_iff measurePreserving_toCircle.measurable.aemeasurable
    (measurableSet_eq_fun hg.measurable measurable_const)).mpr hc

end TriangularBilliards

lemma ae_fst_of_ae_prod {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [NeZero ν] {p : α → Prop}
    (h : ∀ᵐ z ∂μ.prod ν, p z.1) : ∀ᵐ x ∂μ, p x := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  obtain ⟨y,hy⟩ := hx.exists
  exact hy

lemma measure_zero_or_one_of_indicator_constant {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {A : Set α} {c : ℂ}
    (h : A.indicator (fun _ => (1 : ℂ)) =ᵐ[μ] fun _ => c) :
    μ A=0 ∨ μ A=1 := by
  classical
  obtain ⟨x,hx⟩ := h.exists
  by_cases hxA : x∈A
  · have hc : c=1 := by simpa only [indicator_of_mem hxA] using hx.symm
    right
    have he : A =ᵐ[μ] univ := by
      filter_upwards [h] with y hy
      apply propext
      simp only [mem_univ,iff_true]
      by_contra hn
      rw [indicator_of_notMem hn,hc] at hy
      exact zero_ne_one hy
    rw [measure_congr he,measure_univ]
  · have hc : c=0 := by simpa only [indicator_of_notMem hxA] using hx.symm
    left
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [h] with y hy
    intro hym
    rw [indicator_of_mem hym,hc] at hy
    exact one_ne_zero hy

lemma invariant_indicator {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) (T : α → α) (A : Set α) (h : μ ((T ⁻¹' A) ∆ A)=0) :
    (fun x => A.indicator (fun _ => (1:ℂ)) (T x)) =ᵐ[μ] A.indicator (fun _ => (1:ℂ)) := by
  classical
  filter_upwards [measure_symmDiff_eq_zero_iff.mp h] with x hx
  change (T x∈A) = (x∈A) at hx
  by_cases hm : x∈A
  · have ht : T x∈A := by rwa [hx]
    simp only [indicator_of_mem hm,indicator_of_mem ht]
  · have ht : T x∉A := by rwa [hx]
    simp only [indicator_of_notMem hm,indicator_of_notMem ht]

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology

/-- Every bounded measurable invariant of the actual billiard is constant.
Spatial rigidity is proved above on the oriented double; side holonomy now
uses the actual irrational angle, with no Diophantine rate assumption. -/
theorem bounded_billiard_invariant_constant (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    {f : Phase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (phaseMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hinv : ∀ t : ℝ, (fun z => f (billiardFlow Q t z)) =ᵐ[phaseMeasure Q] f) :
    ∃ c : ℂ, f =ᵐ[phaseMeasure Q] fun _ => c := by
  let F : DoublePhase → ℂ := fun z => f z.1
  have hFm : StronglyMeasurable F := hfm.comp_measurable measurable_fst
  have mp : MeasurePreserving (Prod.fst : DoublePhase → Phase) (doubleMeasure Q) (phaseMeasure Q) :=
    measurePreserving_fst
  have hF : MemLp F 2 (doubleMeasure Q) := hf.comp_measurePreserving mp
  have hFi : (geodesicHilbertFlow Q).HasGenerator (hF.toLp F) 0 := by
    apply ((geodesicHilbertFlow Q).hasGenerator_zero_iff _).mpr
    intro t
    apply Lp.ext
    filter_upwards [geodesic_koopman_ae Q t (hF.toLp F),hF.coeFn_toLp,
      (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae hF.coeFn_toLp,
      mp.quasiMeasurePreserving.ae (hinv t)] with z hz hfz hftz hiz
    rw [hz,hftz,hfz]
    exact hiz
  let g : Circle → ℂ := fun v => spatialMean Q F (v,0)
  have hgm : StronglyMeasurable g := (spatialMean_stronglyMeasurable Q hFm).comp_measurable
    (measurable_id.prodMk measurable_const)
  have hgmean (c : DirectionParity) : spatialMean Q F c = g c.1 := rfl
  have hgi (i : Fin 3) : g ∘ reflectedDirection Q i =ᵐ[angularMeasure] g := by
    apply ae_fst_of_ae_prod (ν := parityMeasure)
    have hh := spatialMean_reflection_invariant Q hFm hF (fun z => hb z.1) hFi i
    filter_upwards [hh] with z hz
    exact hz
  obtain ⟨c,hgc⟩ := angular_reflections_constant Q hQ hgm hgi
  have hs := bounded_invariant_spatial_constancy Q hFm hF (fun z => hb z.1) hFi
  have hs' : ∀ᵐ v ∂angularMeasure,
      (fun x => f (x,v)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table] fun _ => g v := by
    apply ae_fst_of_ae_prod (ν := parityMeasure)
    exact hs
  have hh : ∀ᵐ v ∂angularMeasure, ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), f (x,v)=c := by
    filter_upwards [hs',hgc] with v hv hvc
    filter_upwards [hv] with x hx
    exact hx.trans hvc
  refine ⟨c,?_⟩
  have hm : MeasurableSet {z : ℂ × Circle | f z=c} := measurableSet_eq_fun hfm.measurable measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact (Measure.ae_ae_comm (p := fun x v => f (x,v)=c) hm).mpr hh

/-- The invariant-set endpoint, for invariance modulo null sets at every real
(time), on the normalized interior phase space of every irrational triangle. -/
theorem irrational_triangle_invariant_set (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    (A : Set Phase) (hA : MeasurableSet A)
    (hAi : ∀ t : ℝ, phaseMeasure Q (((billiardFlow Q t) ⁻¹' A) ∆ A)=0) :
    phaseMeasure Q A=0 ∨ phaseMeasure Q A=1 := by
  classical
  let f : Phase → ℂ := A.indicator (fun _ => 1)
  have hfm : StronglyMeasurable f := stronglyMeasurable_const.indicator hA
  have hf : MemLp f 2 (phaseMeasure Q) := (memLp_const (1:ℂ)).indicator hA
  have hb (z : Phase) : ‖f z‖ ≤ 1 := by
    by_cases hz : z∈A <;> simp [f,hz]
  obtain ⟨c,hc⟩ := bounded_billiard_invariant_constant Q hQ hfm hf hb
    (fun t => invariant_indicator _ _ _ (hAi t))
  exact measure_zero_or_one_of_indicator_constant hc

/-- Full two-sided billiard ergodicity, including complete regular
chains and the geometric and measure-theoretic guarantees. -/
theorem irrational_triangle_billiard (Q : Triangle) (hQ : Q.HasIrrationalAngle) :
    MainConclusion Q := by
  refine ⟨phaseMeasure_univ Q,ae_exists_chain Q,?_,measurePreserving_billiardFlow Q,
    billiardFlow_cocycle Q,irrational_triangle_invariant_set Q hQ⟩
  intro z c d
  exact FlightChain.unique c d

/-- The same conclusion for the completion of the area-angular measure.
Thus "measurable" may also be read in the Lebesgue-completed sense. -/
theorem irrational_triangle_nullMeasurable_set (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    (A : Set Phase) (hA : NullMeasurableSet A (phaseMeasure Q))
    (hAi : ∀ t : ℝ, phaseMeasure Q (((billiardFlow Q t) ⁻¹' A) ∆ A)=0) :
    phaseMeasure Q A=0 ∨ phaseMeasure Q A=1 := by
  have he : toMeasurable (phaseMeasure Q) A =ᵐ[phaseMeasure Q] A := hA.toMeasurable_ae_eq
  rw [← measure_congr he]
  apply irrational_triangle_invariant_set Q hQ _ (measurableSet_toMeasurable _ _)
  intro t
  apply measure_symmDiff_eq_zero_iff.mpr
  have hpre : (billiardFlow Q t ⁻¹' toMeasurable (phaseMeasure Q) A) =ᵐ[phaseMeasure Q]
      (billiardFlow Q t ⁻¹' A) :=
    (measurePreserving_billiardFlow Q t).quasiMeasurePreserving.ae he
  exact hpre.trans ((measure_symmDiff_eq_zero_iff.mp (hAi t)).trans he.symm)

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
end

end OAI
