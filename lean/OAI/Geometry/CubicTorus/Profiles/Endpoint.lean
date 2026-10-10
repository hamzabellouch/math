import Mathlib
import OAI.Geometry.CubicTorus.Reflection.CoordinateReflection2

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_symmetric_unit_kernel {A : Plane →L[ℝ] Plane}
    (hA : ∀ v w,⟪A v,w⟫=⟪v,A w⟫) {p : Plane} (hp : ‖p‖=1)
    (hk : A p=0) :
    A=(planeTrace A) • (ContinuousLinearMap.id ℝ Plane-(innerSL ℝ p).smulRight p) := by
  let a := A (EuclideanSpace.single 0 1) 0
  let b := A (EuclideanSpace.single 0 1) 1
  let d := A (EuclideanSpace.single 1 1) 1
  have hab : A (EuclideanSpace.single 1 1) 0=b := by
    symm
    exact (by simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hA (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1))
  have hAp (j : Fin 2) := congrArg (fun x : Plane ↦ x j) hk
  rw [plane_decompose p,map_add,map_smul,map_smul] at hAp
  have h0 : a*p 0+b*p 1=0 := by
    have hh := hAp 0
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,PiLp.zero_apply,hab] at hh
    dsimp [a]
    nlinarith
  have h1 : b*p 0+d*p 1=0 := by
    have hh := hAp 1
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,PiLp.zero_apply] at hh
    dsimp [b,d]
    nlinarith
  have hn : (p 0)^2+(p 1)^2=1 := by
    have hh := EuclideanSpace.real_norm_sq_eq p
    rw [hp,one_pow,Fin.sum_univ_two] at hh
    exact hh.symm
  have ha : a=(a+d)*(1-(p 0)^2) := by
    linear_combination p 0*h0-p 1*h1+d*hn
  have hd : d=(a+d)*(1-(p 1)^2) := by
    linear_combination -p 0*h0+p 1*h1+a*hn
  have hb : b= -(a+d)*(p 0)*(p 1) := by
    linear_combination p 1*h0+p 0*h1-b*hn
  have ht : planeTrace A=a+d := by simp only [planeTrace,Fin.sum_univ_two]; rfl
  apply ContinuousLinearMap.ext
  intro u
  conv_lhs => rw [plane_decompose u,map_add,map_smul,map_smul]
  ext i
  fin_cases i <;>
    simp only [ht,smul_apply,sub_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
      PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
  · change u 0*a+u 1*(A (EuclideanSpace.single 1 1) 0)=(a+d)*(u 0-(u 0*p 0+u 1*p 1)*p 0)
    rw [hab]
    linear_combination u 0*ha+u 1*hb
  · change u 0*b+u 1*d=(a+d)*(u 1-(u 0*p 0+u 1*p 1)*p 1)
    linear_combination u 0*hb+u 1*hd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_unit_kernel_shape {n v : Cover} (hn : ‖n‖=1) (hv : ‖v‖=1)
    (hnv : ⟪n,v⟫=0) {D : Cover →L[ℝ] Cover}
    (hD : ∀ w,⟪n,D w⟫=0)
    (hs : ∀ u w,⟪n,u⟫=0 → ⟪n,w⟫=0 → ⟪D u,w⟫=⟪u,D w⟫)
    (hk : D v=0) {w : Cover} (hw : ⟪n,w⟫=0) :
    D w=coverTrace D • (w-⟪v,w⟫ • v) := by
  let L := (normalPlaneLinearIsometry n).toContinuousLinearMap
  let P := normalPlaneCoordinates n
  let A : Plane →L[ℝ] Plane := P.comp (D.comp L)
  have hL (u : Plane) : L u=normalPlaneEmbedding n u := rfl
  have hLP (u : Cover) (hu : ⟪n,u⟫=0) : L (P u)=u :=
    normalPlaneEmbedding_coordinates_of_inner_zero hn hu
  have hLPD (u : Cover) : L (P (D u))=D u := hLP _ (hD u)
  have hP : P=L.adjoint := rfl
  have hAs : ∀ u z,⟪A u,z⟫=⟪u,A z⟫ := by
    intro u z
    change ⟪P (D (L u)),z⟫=⟪u,P (D (L z))⟫
    rw [hP,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
    exact hs _ _ (normalPlaneEmbedding_inner hn u) (normalPlaneEmbedding_inner hn z)
  have hPv : ‖P v‖=1 := by rw [←normalPlaneEmbedding_norm n]; exact (congrArg norm (hLP v hnv)).trans hv
  have hAv : A (P v)=0 := by
    change P (D (L (P v)))=0
    rw [hLP v hnv,hk,map_zero]
  have hA := plane_symmetric_unit_kernel hAs hPv hAv
  have htr : coverTrace D=planeTrace A := by
    calc
      coverTrace D=coverTrace ((D.comp L).comp P) := by
        apply normal_trace_invariance hn hD
        · intro u; exact hD (L (P u))
        · intro u hu
          change D u=D (L (P u))
          rw [hLP u hu]
      _=planeTrace A := rectangular_trace _ _
  have hip : ⟪P v,P w⟫=⟪v,w⟫ := by
    have hh := (normalPlaneLinearIsometry n).inner_map_map (P v) (P w)
    change ⟪L (P v),L (P w)⟫=⟪P v,P w⟫ at hh
    rw [hLP v hnv,hLP w hw] at hh
    exact hh.symm
  calc
    D w=L (A (P w)) := by
      change D w=L (P (D (L (P w))))
      rw [hLP w hw,hLPD]
    _=coverTrace D • (w-⟪v,w⟫ • v) := by
      rw [hA,←htr]
      simp only [smul_apply,sub_apply,
        ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
        map_smul,map_sub,hLP w hw,hLP v hnv,hip]

lemma normal_unit_kernel_trace_square {n v : Cover} (hn : ‖n‖=1) (hv : ‖v‖=1)
    (hnv : ⟪n,v⟫=0) {D : Cover →L[ℝ] Cover}
    (hD : ∀ w,⟪n,D w⟫=0)
    (hs : ∀ u w,⟪n,u⟫=0 → ⟪n,w⟫=0 → ⟪D u,w⟫=⟪u,D w⟫)
    (hk : D v=0) : coverTrace (D.comp D)=(coverTrace D)^2 := by
  let Q : Cover →L[ℝ] Cover := ContinuousLinearMap.id ℝ Cover-
    (innerSL ℝ n).smulRight n-(innerSL ℝ v).smulRight v
  have hQ (w : Cover) : Q w=w-⟪n,w⟫ • n-⟪v,w⟫ • v := rfl
  have hQn (w : Cover) : ⟪n,Q w⟫=0 := by
    rw [hQ,inner_sub_right,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hn,one_pow,mul_one,hnv,mul_zero,sub_self,sub_zero]
  have hvn : ⟪v,n⟫=0 := by simpa only [real_inner_comm] using hnv
  have hQv (w : Cover) : ⟪v,Q w⟫=0 := by
    rw [hQ,inner_sub_right,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hv,one_pow,mul_one,hvn,mul_zero,sub_zero,sub_self]
  have hQQ : Q.comp Q=Q := by
    ext w : 1
    rw [ContinuousLinearMap.comp_apply,hQ,hQn,hQv,zero_smul,zero_smul,sub_zero,sub_zero]
  have hsub (A B : Cover →L[ℝ] Cover) : coverTrace (A-B)=coverTrace A-coverTrace B :=
    coverTraceCLM.map_sub A B
  have htQ : coverTrace Q=1 := by
    simp only [Q,hsub,coverTrace_smulRight,innerSL_apply_apply,
      real_inner_self_eq_norm_sq,hn,hv,one_pow]
    norm_num [coverTrace,Fin.sum_univ_three]
  let B := coverTrace D • Q
  have ht : coverTrace (D.comp D)=coverTrace (B.comp B) := by
    apply normal_trace_square_invariance hn hD
    · intro w
      change ⟪n,coverTrace D • Q w⟫=0
      rw [real_inner_smul_right,hQn,mul_zero]
    · intro w hw
      change D w=coverTrace D • Q w
      rw [hQ,hw,zero_smul,sub_zero]
      exact normal_unit_kernel_shape hn hv hnv hD hs hk hw
  rw [ht]
  change coverTrace ((coverTrace D • Q).comp (coverTrace D • Q))=_
  rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul,hQQ,coverTrace_smul,htQ,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace CubicTorus

theorem measure_eq_of_smooth_bounded_integrals
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ,ContDiff ℝ (⊤ : ℕ∞) f → (∀ x,|f x|≤1) →
      (∫ x,f x ∂μ)=∫ x,f x ∂ν) : μ=ν := by
  apply Measure.ext_of_charFun
  funext t
  apply Complex.ext
  · change RCLike.re (charFun μ t)=RCLike.re (charFun ν t)
    rw [charFun_apply,charFun_apply,← integral_re (𝕜 := ℂ),← integral_re (𝕜 := ℂ)]
    · simpa only [RCLike.re_to_complex,Complex.exp_re,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,Real.exp_zero,one_mul] using
        h (fun x ↦ Real.cos ⟪x,t⟫) (contDiff_id.inner ℝ contDiff_const).cos
          (fun x ↦ Real.abs_cos_le_one _)
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
  · change RCLike.im (charFun μ t)=RCLike.im (charFun ν t)
    rw [charFun_apply,charFun_apply,← integral_im (𝕜 := ℂ),← integral_im (𝕜 := ℂ)]
    · simpa only [RCLike.im_to_complex,Complex.exp_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,Real.exp_zero,one_mul] using
        h (fun x ↦ Real.sin ⟪x,t⟫) (contDiff_id.inner ℝ contDiff_const).sin
          (fun x ↦ Real.abs_sin_le_one _)
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_measure_eq {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    Measure.map (fun z : BlowupNormalBundle ↦ z.1)
      (((ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}).withDensity
        (fun z ↦ ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane ↦ a+normalGraph n g y)
      (volume.withDensity (fun y : Plane ↦
        ENNReal.ofReal (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}
  let G : Plane → Cover := fun y ↦ a+normalGraph n g y
  let w : Plane → ℝ := fun y ↦ φ (G y)*‖graphAreaVector n g y‖
  have hGc : Continuous G := graph_trace_continuous a n hg.continuous continuous_id
  have hwc : Continuous w := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hwi : Integrable w := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hφi : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  let : IsFiniteMeasure (μ.withDensity (fun z : BlowupNormalBundle ↦ ENNReal.ofReal (φ z.1))) :=
    isFiniteMeasure_withDensity_ofReal hφi.hasFiniteIntegral
  let : IsFiniteMeasure (volume.withDensity (fun y : Plane ↦ ENNReal.ofReal (w y))) :=
    isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  change Measure.map (fun z : BlowupNormalBundle ↦ z.1)
    (μ.withDensity (fun z ↦ ENNReal.ofReal (φ z.1))) =
    Measure.map G (volume.withDensity (fun y ↦ ENNReal.ofReal (w y)))
  apply measure_eq_of_smooth_bounded_integrals
  intro f hf hfb
  have hmφ : Measurable (fun z : BlowupNormalBundle ↦ ENNReal.ofReal (φ z.1)) :=
    (hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal
  rw [integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_map hGc.measurable.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hmφ
      (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hwc.measurable.ennreal_ofReal
      (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hwpos (y : Plane) : 0≤w y := mul_nonneg (hφb (G y)).1 (norm_nonneg _)
  simp_rw [ENNReal.toReal_ofReal (hφb _).1,ENNReal.toReal_ofReal (hwpos _),smul_eq_mul]
  have he := cutoff_graph_patch_signed_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb hf hfb
  change (∫ z,φ z.1*f z.1 ∂μ)=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all volume fun y ↦ by dsimp only [w,G]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_graphUnitNormalExtension (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) : Measurable (graphUnitNormalExtension a n g) := by
  have hgrad : Measurable (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  exact (graphSlopeNormal_contDiff hn).continuous.measurable.comp
    (hgrad.comp ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))

theorem cutoff_graph_patch_normal_measure_eq {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (((ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}).withDensity
      (fun z ↦ ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane ↦ (a+normalGraph n g y,
      (⟨graphSlopeNormal n (gradient g y),graphSlopeNormal_unit hn _⟩ : NormalSphere)))
      (volume.withDensity (fun y : Plane ↦
        ENNReal.ofReal (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}
  let η := μ.withDensity (fun z ↦ ENNReal.ofReal (φ z.1))
  let L : Cover → BlowupNormalBundle := fun x ↦
    (x,⟨graphUnitNormalExtension a n g x,graphUnitNormalExtension_unit a hn g x⟩)
  have hL : Measurable L := measurable_id.prodMk
    (measurable_graphUnitNormalExtension a hn g).subtype_mk
  have hmap : Measure.map L (Measure.map Prod.fst η)=η := by
    rw [Measure.map_map hL measurable_fst]
    have hae : L ∘ Prod.fst =ᵐ[η] id := by
      apply (ae_withDensity_iff
        (show Measurable (fun z : BlowupNormalBundle ↦ ENNReal.ofReal (φ z.1)) from
          (hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal)).mpr
      have hnrm := cutoff_graph_patch_normal_ae hA a hn hg hc hgraph hsat hflux
        hφ hsφ hφU hφO hφR hφb
      filter_upwards [hnrm] with z hz hpos
      have hφpos : 0<φ z.1 := by
        by_contra hh
        exact hpos (ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hh))
      apply Prod.ext
      · rfl
      apply Subtype.ext
      exact (hz hφpos).symm
    rw [Measure.map_congr hae,Measure.map_id]
  have hm := cutoff_graph_patch_measure_eq hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb
  change Measure.map Prod.fst η=_ at hm
  change η=_
  have hG : Measurable (fun y : Plane ↦ a+normalGraph n g y) := by
    simpa only [id_eq] using (graph_trace_continuous a n hg.continuous continuous_id).measurable
  rw [← hmap,hm,Measure.map_map hL hG]
  congr 1
  funext y
  apply Prod.ext
  · rfl
  apply Subtype.ext
  exact graphUnitNormalExtension_graph a hn g g y

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map f (μ.withDensity (w ∘ f))=(Measure.map f μ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs,
    Measure.restrict_map hf hs,lintegral_map hw hf]
  rfl

lemma projected_cutoff_measure {ν : Measure BlowupNormalBundle} {O : Set Cover}
    (hO : MeasurableSet O) {φ : Cover → ℝ} (hφ : Measurable φ) :
    Measure.map Prod.fst ((ν.restrict {z | z.1∈O}).withDensity
      (fun z ↦ ENNReal.ofReal (φ z.1)))=
      ((Measure.map Prod.fst ν).restrict O).withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
  change Measure.map Prod.fst ((ν.restrict (Prod.fst ⁻¹' O)).withDensity
    ((fun x ↦ ENNReal.ofReal (φ x)) ∘ Prod.fst))=_
  rw [sibling_map_withDensity_comp _ measurable_fst hφ.ennreal_ofReal,
    ← Measure.restrict_map measurable_fst hO]

lemma normalCoverMeasure_reverse_projected (μ : FiniteMeasure NormalBundle) :
    Measure.map Prod.fst (normalCoverMeasure (μ.map reverseNormal) : Measure BlowupNormalBundle)=
      Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle) := by
  simp only [normalCoverMeasure,FiniteMeasure.toMeasure_map]
  rw [Measure.map_map continuous_normalCoverMap.measurable continuous_reverseNormal.measurable,
    Measure.map_map measurable_fst
      (continuous_normalCoverMap.measurable.comp continuous_reverseNormal.measurable),
    Measure.map_map measurable_fst continuous_normalCoverMap.measurable]
  rfl

theorem normalMeasure_graph_patch_measure_eq {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1) :
    ((Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle)).restrict
      {x | ∀ i,0<x i ∧ x i<1}).withDensity (fun x ↦ ENNReal.ofReal (φ x))=
    Measure.map (fun y : Plane ↦ a+normalGraph n g y)
      (volume.withDensity (fun y : Plane ↦
        ENNReal.ofReal (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  have hO : MeasurableSet {x : Cover | ∀ i,0<x i ∧ x i<1} := by measurability
  have hflux {F : Set Torus} (hF : MeasurableSet F) {η : FiniteMeasure NormalBundle}
      (hη : IsNormalMeasure F η) (X : Cover → Cover) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
      (hs : HasCompactSupport X) (hXO : tsupport X⊆{x | ∀ i,0<x i ∧ x i<1})
      (_hb : ∀ x,‖X x‖≤1) := normalCoverMeasure_local_flux hF hη hX hs hXO
  rcases hphase with hp|hp
  · have hp' : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x) := by
      simpa only [graphSignedHeight,sub_neg,mem_preimage] using hp
    have hm := cutoff_graph_patch_measure_eq (hE.preimage measurable_quotientMap)
      a hn hg hc hp' (normalMeasure_cutoff_saturation hμ _) (hflux hE hμ)
      hφ hsφ hφU hφO hφR hφb
    rwa [projected_cutoff_measure hO hφ.continuous.measurable] at hm
  · have hp' : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ graphHeightExtension a n g x<⟪n,x-a⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hp
    have hp'' := graph_superlevel_compl_ae a hn hg.continuous hp'
    have hμ' := isNormalMeasure_compl hE hμ
    have hm := cutoff_graph_patch_measure_eq (hE.compl.preimage measurable_quotientMap)
      a hn hg hc hp'' (normalMeasure_cutoff_saturation hμ' _) (hflux hE.compl hμ')
      hφ hsφ hφU hφO hφR hφb
    rwa [projected_cutoff_measure hO hφ.continuous.measurable,
      normalCoverMeasure_reverse_projected] at hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem centered_graph_phase_patch_of_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0<r)
    {K : ℝ≥0} (hg : LipschitzWith K g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (R ρ : ℝ) (U : Set Cover), R<r ∧
      ‖n‖=1 ∧ LipschitzWith K g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
      U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
      (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
       (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))) := by
  let R := r/2
  let s := min (r/4) (1/8)
  have hR : 0<R := half_pos hr
  have hs : 0<s := lt_min (by positivity) (by norm_num)
  have hsR : s<R := by dsimp [s,R]; exact (min_le_left _ _).trans_lt (by linarith)
  have hcell : Metric.ball cubeCenter s ⊆ {x | ∀ i, 0<x i ∧ x i<1} := by
    let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
    apply Metric.ball_subset_closedBall.trans
    exact MovingCenter.closedBall_interior (c := c) (by
      have hh : s≤1/8 := min_le_right _ _
      linarith)
  have hb (x : Cover) (hx : x∈Metric.ball cubeCenter s) :
      quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter := by
    have hx' : x-cubeCenter∈Metric.ball (0 : Cover) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      have hh : ‖x-cubeCenter‖<s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      have hsr : s<r := by dsimp [R] at hsR; linarith
      exact hh.trans hsr
    simpa only [add_sub_cancel] using hcover (x-cubeCenter) hx'
  have hlift (x : Cover) (hx : x∈Metric.ball cubeCenter s) :=
    isMinimizerAt_lifted_boundary hV hE hmin (hcell hx)
  have hp : cubeCenter∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    (hlift cubeCenter (Metric.mem_ball_self hs)).mpr hcenter
  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases
    (hE.preimage measurable_quotientMap) cubeCenter hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)) hp
    (fun x hx ha ↦ (hb x hx).mp ((hlift x hx).mp ha))
  obtain ⟨t,ht,htW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let ρ := t/3
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨R,ρ,W,by dsimp [R]; linarith,hn,hg,hg0,hR,hρ,?_,hW,?_,?_,hWU.trans hcell,
    fun x hx ↦ hb x (hWU hx),hphase.symm⟩
  · intro y hy
    apply hgC.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    apply Metric.closedBall_subset_ball _ hy
    dsimp [R]
    linarith
  · exact (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans htW
  · exact hWU.trans (Metric.ball_subset_ball hsR.le)

theorem actual_centered_compact_normal_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ) (K : ℝ≥0),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ LipschitzWith K f ∧
      f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hgraph,hcover⟩ :=
    actual_centered_normal_graph_chart hV hE hmin hcenter hμ hN hp hae
  let b : ContDiffBump (0 : Plane) := ⟨1,2,by norm_num,by norm_num⟩
  let f : Plane → ℝ := fun y ↦ b y*g y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul hg
  have hs : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := hf.lipschitzWith_of_hasCompactSupport hs (by simp)
  have he : f=ᶠ[𝓝 (0 : Plane)]g := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by norm_num : (0:ℝ)<1)] with y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]
  have hgrad : ∀ᶠ y in 𝓝 (0 : Plane),gradient f y=gradient g y := by
    filter_upwards [he.eventually_nhds] with y hy
    have hey : f=ᶠ[𝓝 y]g := hy
    simp only [gradient,hey.fderiv_eq]
  have hplane : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  refine ⟨n,f,σ,K,hn,hf,hs,hK,he.eq_of_nhds.trans hg0,hσ,?_,?_⟩
  · filter_upwards [he,hgrad,hgraph] with y hy hdy hgy
    simpa only [normalGraph,hy,hdy] using hgy
  · filter_upwards [hplane.eventually he,hcover] with v hv hcv
    simpa only [normalGraph,hv] using hcv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_small_slope_normal_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (_hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),‖gradient f y‖≤(1/4 : ℝ)) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,hf,hfg⟩ := smooth_graph_extension hr hgc
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x ((Metric.ball_subset_ball (by linarith)) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (by linarith : 0<r/2)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hdc (y : Plane) (hy : y∈Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hgC y hy).continuousAt_fderiv (by norm_num)
  have hNfg (x : Cover) (hx : x∈tsupport φ) :
      graphUnitNormalExtension cubeCenter n f x=graphUnitNormalExtension cubeCenter n g x := by
    have hpp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hpp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      refine ⟨-1,Or.inr rfl,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  let F : Cover → Cover := fun x ↦ φ x • (N x-σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    (hN.sub ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ))
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0≤cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),latticePeriodize F z.1=(0 : Cover) := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • (N z.1-σ • graphUnitNormalExtension cubeCenter n f z.1)=0
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos,sub_self,smul_zero]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      rw [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize F x=0 :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (latticePeriodize_contDiff hF hsF).continuous continuous_const
      (latticePeriodize_periodic F) (fun _ _ ↦ rfl) hz x hx
  have hf0 : f 0=0 := (hfg (by simpa using (half_pos hr))).trans hg0
  have ht : Tendsto (fun y ↦ cubeCenter+normalGraph n f y) (𝓝 (0 : Plane)) (𝓝 cubeCenter) := by
    have hc : Continuous (fun y ↦ cubeCenter+normalGraph n f y) :=
      continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
        (hf.continuous.smul continuous_const))
    have hz : cubeCenter+normalGraph n f 0=cubeCenter := by
      simp only [normalGraph,hf0,zero_smul,add_zero]
      change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
      rw [map_zero,add_zero]
    simpa only [ContinuousAt,hz] using hc.continuousAt (x := 0)
  have hone : ∀ᶠ x in 𝓝 cubeCenter,φ x=1 := by
    filter_upwards [Metric.ball_mem_nhds cubeCenter hρ] with x hx
    exact radialHeightCutoff_one hρ (Metric.ball_subset_closedBall hx)
  have hsmall : ∀ᶠ y in 𝓝 (0 : Plane),‖gradient f y‖≤(1/4 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (half_pos hr)] with y hy
    have he : f=ᶠ[𝓝 y]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      exact hfg hz
    rw [plane_gradient_norm,he.fderiv_eq]
    exact norm_fderiv_le_of_lipschitz ℝ hg
  refine ⟨n,f,σ,hn,hf,hf0,hσ,hsmall,?_,?_⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually hone,Metric.ball_mem_nhds (0 : Plane) (half_pos hr)]
      with y hey hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hzero := hb _ hby
    rw [hey] at hzero
    change φ (cubeCenter+normalGraph n f y) •
      (N (cubeCenter+normalGraph n f y)-σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y))=0 at hzero
    rw [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hzero
    exact ⟨sub_eq_zero.mp hzero,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

theorem actual_centered_compact_small_normal_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ) (K : ℝ≥0),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ LipschitzWith K f ∧
      f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),‖gradient f y‖≤(1/4 : ℝ)) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hsmall,hgraph,hcover⟩ :=
    actual_centered_small_slope_normal_chart hV hE hmin hcenter hμ hN hp hae
  let b : ContDiffBump (0 : Plane) := ⟨1,2,by norm_num,by norm_num⟩
  let f : Plane → ℝ := fun y ↦ b y*g y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul hg
  have hs : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := hf.lipschitzWith_of_hasCompactSupport hs (by simp)
  have he : f=ᶠ[𝓝 (0 : Plane)]g := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by norm_num : (0:ℝ)<1)] with y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]
  have hgrad : ∀ᶠ y in 𝓝 (0 : Plane),gradient f y=gradient g y := by
    filter_upwards [he.eventually_nhds] with y hy
    have hey : f=ᶠ[𝓝 y]g := hy
    simp only [gradient,hey.fderiv_eq]
  have hplane : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  refine ⟨n,f,σ,K,hn,hf,hs,hK,he.eq_of_nhds.trans hg0,hσ,?_,?_,?_⟩
  · filter_upwards [hgrad,hsmall] with y hy hsmall
    rwa [hy]
  · filter_upwards [he,hgrad,hgraph] with y hy hdy hgy
    simpa only [normalGraph,hy,hdy] using hgy
  · filter_upwards [hplane.eventually he,hcover] with v hv hcv
    simpa only [normalGraph,hv] using hcv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_map_volume_le_of_lower_density
    (σ : FiniteMeasure Torus) (B : Set Torus)
    {R c : ℝ} (hR : 0<R) (hc : 0<c)
    (hl : ∀ a∈B,∀ r : ℝ,0<r → r≤R →
      c*r^2≤(σ : Measure Torus).real (Metric.ball a r))
    {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (a : Torus) (D : Set Plane)
    (hF : Measurable (fun y ↦ a+quotientMap (normalGraph n g y)))
    (hsmall : ∀ y∈D,‖normalGraph n g y‖<1/4)
    (hB : ∀ y∈D,a+quotientMap (normalGraph n g y)∈B) :
    Measure.map (fun y ↦ a+quotientMap (normalGraph n g y)) (volume.restrict D)≤
      ((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c))•(σ : Measure Torus) := by
  let F : Plane → Torus := fun y ↦ a+quotientMap (normalGraph n g y)
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.map_apply hF hT,Measure.restrict_apply (hT.preimage hF),
    Measure.smul_apply,smul_eq_mul]
  have he : F ⁻¹' T∩D={y∈D | F y∈T∩B} := by
    ext y
    exact ⟨fun hy ↦ ⟨hy.2,hy.1,hB y hy.2⟩,fun hy ↦ ⟨hy.2.1,hy.1⟩⟩
  change volume (F ⁻¹' T∩D)≤_
  rw [he]
  have hh := normalGraph_preimage_volume_le hn g a D hsmall (T∩B)
  have ha := hausdorff_two_le_measure_of_lower_density σ (T∩B) hR hc (fun x hx ↦ hl x hx.2)
  calc
    _≤(planeAreaFactor : ℝ≥0∞)*Measure.hausdorffMeasure 2 (T∩B) := hh
    _≤(planeAreaFactor : ℝ≥0∞)*(ENNReal.ofReal (64/c)*(σ : Measure Torus) (T∩B)) :=
      mul_le_mul_right ha _
    _≤((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c))*(σ : Measure Torus) T := by
      rw [mul_assoc]
      exact mul_le_mul_right (mul_le_mul_right
        (show (σ : Measure Torus) (T∩B)≤(σ : Measure Torus) T from measure_mono inter_subset_left) _) _

theorem isMinimizerAt_dominated_normal_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (s r : ℝ) (C : ℝ≥0∞),
      ‖n‖=1 ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ g 0=0 ∧ (s=1 ∨ s= -1) ∧
      0<r ∧ C≠⊤ ∧
      (∀ y∈Metric.closedBall (0 : Plane) r,
        N (x+normalGraph n g y)=s•graphSlopeNormal n (gradient g y) ∧
        quotientMap (x+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      Measure.map (fun y : Plane ↦ quotientMap (x+normalGraph n g y))
        (volume.restrict (Metric.closedBall 0 r))≤C•(spatialNormalMeasure μ : Measure Torus) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,s,hn,hg,hg0,hs,hgraph,hcover⟩ := isMinimizerAt_normal_graph_chart
    hV hE hmin hμ hN hp hae x hx
  have hgC : Continuous (normalGraph n g) :=
    (normalPlaneLinearIsometry n).continuous.add (hg.continuous.smul continuous_const)
  have hzero : normalGraph n g 0=0 := by
    change normalPlaneLinearIsometry n 0+g 0•n=0
    simp [hg0]
  have hsmall : ∀ᶠ y in 𝓝 (0 : Plane),‖normalGraph n g y‖<(1/4 : ℝ) :=
    (isOpen_lt hgC.norm continuous_const).mem_nhds (by change ‖normalGraph n g 0‖<(1/4 : ℝ); rw [hzero,norm_zero]; norm_num)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hgraph.and hsmall)
  have hrb : Metric.closedBall (0 : Plane) (r/2)⊆Metric.ball 0 r :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨R,c,hR,hc,hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c)
  refine ⟨n,g,s,r/2,C,hn,hg,hg0,hs,by positivity,by dsimp [C]; finiteness,
    (fun y hy ↦ (hrsub (hrb hy)).1),?_,hcover⟩
  have hF : Measurable (fun y ↦ quotientMap x+quotientMap (normalGraph n g y)) :=
    (continuous_const.add (continuous_quotientMap.comp hgC)).measurable
  have hdom := normalGraph_map_volume_le_of_lower_density (spatialNormalMeasure μ)
    (frontier (openRepresentative E)) hR hc
    (fun a ha ↦ hl μ hμ a (by rwa [← isMinimizerAt_frontier_openRepresentative hV hE hmin]))
    hn g (quotientMap x) (Metric.closedBall 0 (r/2)) hF
    (fun y hy ↦ (hrsub (hrb hy)).2)
    (fun y hy ↦ by simpa only [← quotientMap_add] using (hrsub (hrb hy)).1.2)
  simpa only [← quotientMap_add] using hdom

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
