import OAI.Geometry.QuadricBundles.WeakBaseChange

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma matrix_coefficients_inverse (c : MatrixCoefficients) :
    matrixToCoefficients (coefficientsToMatrix c)=c := by ext p; rfl

lemma traceScalar_tendsto {ex : ℕ → ℕ} (hex : Tendsto ex atTop atTop)
    (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    Tendsto (fun k ↦ traceScalar (ex k) i j z) atTop (𝓝 1) := by
  have hn : ‖polarizationTransition i j (affineQuadric i z)‖≠0 := by
    rw [norm_ne_zero_iff,polarizationTransition_affine]
    exact mul_ne_zero (firstFactor_ne_zero hz) (secondFactor_ne_zero hz)
  simpa only [traceScalar,Real.rpow_zero,Function.comp_def] using
    (Real.continuousAt_const_rpow (b := 0) hn).tendsto.comp
      ((tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp hex)

def coefficientFrame (D : EqualizerData) (i j : StandardChart) (z : BaseCoordinates) :
    CoefficientSpace →L[ℝ] CoefficientSpace :=
  (congruenceCoefficients (D.coordinateTransition i j z).transpose).restrictScalars ℝ

lemma coefficientFrame_continuousOn (D : EqualizerData) (i j : StandardChart) :
    ContinuousOn (coefficientFrame D i j) (coordinateOverlap i j) :=
  (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn
    (continuous_congruenceCoefficients.comp_continuousOn
      (by
        apply continuousOn_pi.mpr; intro a
        apply continuousOn_pi.mpr; intro b
        exact continuousOn_pi.mp (continuousOn_pi.mp (D.coordinateTransition_continuousOn i j) b) a))

lemma coefficientFrame_bounded (D : EqualizerData) (i j : StandardChart)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∃ C : ℝ, 0≤C ∧ ∀ z∈K, ‖coefficientFrame D i j z‖≤C := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image ((coefficientFrame_continuousOn D i j).mono hKU).norm
  exact ⟨max C 0,le_max_right _ _,fun z hz ↦ (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma coefficients_eq (k : ℕ) (a : TraceIndex) :
    X.f k a =ᵐ[volume] fun x ↦ matrixToCoefficients (cutoffTrace (P k) a x) := by
  filter_upwards [X.coefficients k a] with x hx
  rw [← matrix_coefficients_inverse (X.f k a x),hx]

lemma coefficients_change {a b : TraceIndex} {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap a.1 b.1)
    (hKa : K ⊆ traceSupport a)
    (hKb : MapsTo (coordinateChange a.1 b.1) K (traceSupport b)) (k : ℕ) :
    ∀ᵐ x ∂volume.restrict K,
      X.f k a x=traceScalar (ex k) a.1 b.1 x •
        coefficientFrame D a.1 b.1 x (X.f k b (coordinateChange a.1 b.1 x)) := by
  obtain ⟨C,_,hC⟩ := coordinateChange_compact_bound a.1 b.1 hK hKU
  have hq : Measure.QuasiMeasurePreserving (coordinateChange a.1 b.1) (volume.restrict K) volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hC⟩
  filter_upwards [ae_restrict_of_ae (X.coefficients_eq k a),hq.ae (X.coefficients_eq k b),
    ae_restrict_mem hK.measurableSet] with x ha hb hx
  rw [ha,hb,cutoffTrace_eq _ _ (hKa hx),cutoffTrace_eq _ _ (hKb hx),
    (P k).matrix_compatible a.1 b.1 (hKU hx)]
  change matrixToCoefficients (_ • _) = _
  rfl

lemma weak_coefficients_change (hex : Tendsto ex atTop atTop)
    {a b : TraceIndex} {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap a.1 b.1)
    (hKa : K ⊆ traceSupport a)
    (hKb : MapsTo (coordinateChange a.1 b.1) K (traceSupport b)) :
    ∀ᵐ x ∂volume.restrict K,
      X.w a x=coefficientFrame D a.1 b.1 x (X.w b (coordinateChange a.1 b.1 x)) := by
  let μ := volume.restrict K
  let T := coordinateChange a.1 b.1
  let F := coefficientFrame D a.1 b.1
  have : IsFiniteMeasure μ := ⟨by
    change volume.restrict K univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨J,_,hJ⟩ := coordinateChange_compact_bound a.1 b.1 hK hKU
  have hq : Measure.QuasiMeasurePreserving T μ volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hJ⟩
  obtain ⟨C,hC,hFC⟩ := coefficientFrame_bounded D a.1 b.1 hK hKU
  have hFm : AEStronglyMeasurable F μ :=
    ((coefficientFrame_continuousOn D a.1 b.1).mono hKU).aestronglyMeasurable hK.measurableSet
  have hFb : ∀ᵐ x ∂μ, ‖F x‖≤C := (ae_restrict_mem hK.measurableSet).mono hFC
  let B : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    boundedCompositionLp measurable_id ENNReal.one_ne_top (by
      simpa only [Measure.map_id,one_smul] using (Measure.restrict_le_self (μ := volume) (s := K)))
  let A₀ : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    boundedCompositionLp (coordinateChange_measurable a.1 b.1) ENNReal.ofReal_ne_top hJ
  let A : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    (boundedMultiplierLp hFm hC hFb).comp A₀
  have hB (f : CoefficientL2) : B f =ᵐ[μ] f := by
    exact boundedCompositionLp_coe measurable_id ENNReal.one_ne_top _ f
  have hA (f : CoefficientL2) : A f =ᵐ[μ] fun x ↦ F x (f (T x)) := by
    filter_upwards [boundedMultiplierLp_coe hFm hC hFb (A₀ f),
      boundedCompositionLp_coe (coordinateChange_measurable a.1 b.1) ENNReal.ofReal_ne_top hJ f]
      with x hx hy
    change boundedMultiplierLp hFm hC hFb (A₀ f) x = _
    rw [hx,hy]
  let u (k : ℕ) := X.f (X.subsequence k) b
  let v (k : ℕ) := X.f (X.subsequence k) a
  let e (k : ℕ) := B (v k)-A (u k)
  have hu (k : ℕ) : ∀ᵐ x ∂μ, ‖F x (u k (T x))‖≤C*(8*traceBound D b) := by
    filter_upwards [hq.ae (X.bound (X.subsequence k) b),hFb] with x hx hy
    exact (F x).le_opNorm _ |>.trans
      (mul_le_mul hy hx.1 (norm_nonneg _) hC)
  have he (k : ℕ) : e k =ᵐ[μ] fun x ↦
      (traceScalar (ex (X.subsequence k)) a.1 b.1 x-1) • F x (u k (T x)) := by
    filter_upwards [Lp.coeFn_sub (B (v k)) (A (u k)),hB (v k),hA (u k),
      X.coefficients_change hK hKU hKa hKb (X.subsequence k)] with x hsub hv hu hc
    change (B (v k)-A (u k)) x = _
    rw [hsub,Pi.sub_apply,hv,hu]
    change X.f (X.subsequence k) a x - _ = _
    rw [hc,sub_smul,one_smul]
  have hb (k : ℕ) : ∀ᵐ x ∂μ, ‖e k x‖≤8*traceBound D a+C*(8*traceBound D b) := by
    filter_upwards [Lp.coeFn_sub (B (v k)) (A (u k)),hB (v k),hA (u k),
      ae_restrict_of_ae (X.bound (X.subsequence k) a),hu k] with x hsub hv hu hvb hub
    change ‖(B (v k)-A (u k)) x‖≤_
    rw [hsub,Pi.sub_apply,hv,hu]
    exact (norm_sub_le _ _).trans (add_le_add hvb.1 hub)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ e k x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr he,ae_all_iff.mpr hu,ae_restrict_mem hK.measurableSet]
      with x hx hb hxK
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hs := (traceScalar_tendsto (hex.comp X.strictMono.tendsto_atTop) a.1 b.1 (hKU hxK)).sub
      (tendsto_const_nhds (x := (1:ℝ)))
    have ht : Tendsto (fun k ↦ ‖traceScalar (ex (X.subsequence k)) a.1 b.1 x-1‖ *
        (C*(8*traceBound D b))) atTop (𝓝 0) := by simpa using hs.norm.mul_const (C*(8*traceBound D b))
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ ht
    intro k
    rw [hx,norm_smul]
    exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _)
  let : InnerProductSpace ℝ CoefficientSpace := InnerProductSpace.rclikeToReal ℂ CoefficientSpace
  have herr : Tendsto (fun k ↦ ‖e k‖) atTop (𝓝 0) :=
    L2_norm_tendsto_zero_of_bounded_ae e
      (add_nonneg (mul_nonneg (by positivity) (traceBound_nonneg D a))
        (mul_nonneg hC (mul_nonneg (by positivity) (traceBound_nonneg D b)))) hb hlim
  have hw : B (X.w a)=A (X.w b) :=
    real_weakLimit_two_maps A B (X.weak b) (X.weak a) herr
  filter_upwards [hB (X.w a),hA (X.w b)] with x hx hy
  rw [← hx,hw,hy]

end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma coordinateChange_differentiableOn (i j : StandardChart) :
    DifferentiableOn ℂ (coordinateChange i j) (coordinateOverlap i j) := by
  apply DifferentiableOn.prodMk
  · by_cases h : i.1=j.1
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact differentiableOn_fst.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).1.resolve_left h)
  · by_cases h : i.2=j.2
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact differentiableOn_snd.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).2.resolve_left h)

lemma coordinateFiberChange_differentiableOn (D : EqualizerData) (i j : StandardChart)
    (v : FiberCoordinates) : DifferentiableOn ℂ
      (fun z ↦ (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v))
      (coordinateOverlap i j) := by
  apply (coordinateChange_differentiableOn i j).prodMk
  apply differentiableOn_pi.mpr
  intro a
  change DifferentiableOn ℂ (fun z ↦ ∑ b : Fin 2, D.coordinateTransition i j z b a * v b) _
  apply DifferentiableOn.fun_sum
  intro b _
  exact (((D.coordinateTransition_regular i j b a).regular.analyticOnNhd
    (coordinateOverlap_open i j)).differentiableOn).mul_const (v b)

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma globalValue_representative_ae (i : StandardChart) (n : ℕ)
    {K : Set BaseCoordinates} (hKn : K ⊆ traceInterior (i,n)) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=quadraticValue (coefficientsToMatrix (X.w (i,n) x)) v := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hKn (X.representative (i,n)),
    ae_restrict_mem (μ := volume) (s := traceInterior (i,n)) measurableSet_ball |>
      ae_restrict_of_ae_restrict_of_subset hKn] with x hx hxU
  intro v
  rw [X.globalValue_eq_value i n hxU]
  change quadraticValue (X.matrix (i,n) x) v = _
  rw [hx]

lemma globalValue_composed_representative_ae (i j : StandardChart) (m : ℕ)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j)
    (hmap : MapsTo (coordinateChange i j) K (traceInterior (j,m))) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue j (coordinateChange i j x,v)=
        quadraticValue (coefficientsToMatrix (X.w (j,m) (coordinateChange i j x))) v := by
  obtain ⟨C,_,hC⟩ := coordinateChange_compact_bound i j hK hKU
  have hq : Measure.QuasiMeasurePreserving (coordinateChange i j) (volume.restrict K) volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hC⟩
  have hrb : ∀ᵐ x ∂volume, x∈traceInterior (j,m) →
      X.matrix (j,m) x=coefficientsToMatrix (X.w (j,m) x) :=
    (ae_restrict_iff' measurableSet_ball).mp (X.representative (j,m))
  filter_upwards [hq.ae hrb,ae_restrict_mem hK.measurableSet] with x hb hx
  intro v
  rw [X.globalValue_eq_value j m (hmap hx)]
  change quadraticValue (X.matrix (j,m) (coordinateChange i j x)) v = _
  rw [hb (hmap hx)]

lemma coefficientFrame_quadraticValue (D : EqualizerData) (i j : StandardChart)
    (x : BaseCoordinates) (c : CoefficientSpace) (v : FiberCoordinates) :
    quadraticValue (coefficientsToMatrix (coefficientFrame D i j x c)) v =
      quadraticValue (coefficientsToMatrix c) ((D.coordinateTransition i j x).transpose.mulVec v) :=
  quadraticValue_congruence _ _ _

lemma globalValue_change_ae_indices (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    (n m : ℕ) {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j)
    (hn : K ⊆ traceInterior (i,n))
    (hm : MapsTo (coordinateChange i j) K (traceInterior (j,m))) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=X.globalValue j
        (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  have hKa : K ⊆ traceSupport (i,n) := hn.trans ((traceInterior_subset_domain _).trans (traceDomain_subset_support _))
  have hKb : MapsTo (coordinateChange i j) K (traceSupport (j,m)) :=
    fun x hx ↦ traceDomain_subset_support _ (traceInterior_subset_domain _ (hm hx))
  have he := X.weak_coefficients_change hex (a := (i,n)) (b := (j,m)) hK hKU hKa hKb
  filter_upwards [he,X.globalValue_representative_ae i n hn,
    X.globalValue_composed_representative_ae i j m hK hKU hm] with x he ha hb
  intro v
  calc
    X.globalValue i (x,v) = quadraticValue (coefficientsToMatrix (X.w (i,n) x)) v := ha v
    _ = quadraticValue (coefficientsToMatrix (coefficientFrame D i j x
        (X.w (j,m) (coordinateChange i j x)))) v := congrArg (fun c ↦ quadraticValue (coefficientsToMatrix c) v) he
    _ = quadraticValue (coefficientsToMatrix (X.w (j,m) (coordinateChange i j x)))
        ((D.coordinateTransition i j x).transpose.mulVec v) := coefficientFrame_quadraticValue D i j x _ v
    _ = _ := (hb _).symm

lemma globalValue_change_ae (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=X.globalValue j
        (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  obtain ⟨n,hn⟩ := exists_traceInterior_of_compact i hK
  have hTK := hK.image_of_continuousOn ((coordinateChange_differentiableOn i j).continuousOn.mono hKU)
  obtain ⟨m,hm⟩ := exists_traceInterior_of_compact j hTK
  exact X.globalValue_change_ae_indices hex i j n m hK hKU hn
    (fun x hx ↦ hm (mem_image_of_mem _ hx))

lemma globalValue_change (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    {x : BaseCoordinates} (hx : x∈coordinateOverlap i j) (v : FiberCoordinates) :
    X.globalValue i (x,v)=X.globalValue j
      (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (coordinateOverlap_open i j) x hx
  let ρ := r/2
  have hρ : 0<ρ := by dsimp [ρ]; linarith
  have hcb : closedBall x ρ ⊆ coordinateOverlap i j := by
    intro y hy
    exact hball (lt_of_le_of_lt hy (by change r/2 < r; linarith))
  have hb : ball x ρ ⊆ coordinateOverlap i j := ball_subset_closedBall.trans hcb
  let q (z : BaseCoordinates) := X.globalValue i (z,v)
  let s (z : BaseCoordinates) := X.globalValue j
    (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v)
  have hq : DiskPshOn (ball x ρ) q := (X.globalValue_psh i).comp (by fun_prop) (mapsTo_univ _ _)
  have hs : DiskPshOn (ball x ρ) s := (X.globalValue_psh j).comp
    ((coordinateFiberChange_differentiableOn D i j v).mono hb) (mapsTo_univ _ _)
  have he : q =ᵐ[volume.restrict (ball x ρ)] s :=
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall
      (X.globalValue_change_ae hex i j (isCompact_closedBall x ρ) hcb)).mono fun z hz ↦ hz v
  exact hq.eqOn_of_ae isOpen_ball hs
    (fun z _ ↦ X.globalValue_nonneg i (z,v)) (fun z _ ↦ X.globalValue_nonneg j _) he (mem_ball_self hρ)
end ExtractedTrace
end
end QuadricCounterexample

end

end OAI
