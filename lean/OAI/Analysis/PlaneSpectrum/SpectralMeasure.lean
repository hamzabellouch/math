import OAI.Analysis.PlaneSpectrum.Representations

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
lemma inner_toLp (f g : C(X,ℂ)) :
    ⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f, ContinuousMap.toLp 2 (measure Φ v) ℂ g⟫_ℂ =
      ⟪Φ f v,Φ g v⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (star f*g) x ∂measure Φ v := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) f,
        ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) g] with x hx hy
      simp only [hx,hy,RCLike.inner_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply,Complex.star_def]
      ring
    _ = ⟪v,Φ (star f*g) v⟫_ℂ := integral_complex Φ v _
    _ = _ := by
      rw [map_mul,map_star]
      change ⟪v,star (Φ f) (Φ g v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
def vectorLinear : C(X,ℂ) →ₗ[ℂ] H where
  toFun f := Φ f v
  map_add' f g := by simp
  map_smul' c f := by simp
lemma norm_toLp (f : C(X,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure Φ v) ℂ f‖ = ‖vectorLinear Φ v f‖ := by
  have he := congrArg Complex.re (inner_toLp Φ v f f)
  change RCLike.re (⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f,ContinuousMap.toLp 2 (measure Φ v) ℂ f⟫_ℂ) =
    RCLike.re (⟪Φ f v,Φ f v⟫_ℂ) at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
def cyclicMap : Lp ℂ 2 (measure Φ v) →L[ℂ] H :=
  (vectorLinear Φ v).extendOfNorm (ContinuousMap.toLp 2 (measure Φ v) ℂ).toLinearMap
lemma cyclicMap_toLp (f : C(X,ℂ)) :
    cyclicMap Φ v (ContinuousMap.toLp 2 (measure Φ v) ℂ f) = Φ f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)
  · exact ⟨1,fun g => by simp only [one_mul]; exact le_of_eq (norm_toLp Φ v g).symm⟩
lemma norm_cyclicMap (f : Lp ℂ 2 (measure Φ v)) : ‖cyclicMap Φ v f‖ = ‖f‖ := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) f
  obtain ⟨g,rfl⟩ := hy
  rw [cyclicMap_toLp]
  exact (norm_toLp Φ v g).symm
def cyclicIsometry : Lp ℂ 2 (measure Φ v) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap Φ v).toLinearMap,norm_cyclicMap Φ v⟩
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
def mulLp (f : Func X) (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((memLp μ f ∞).fun_mul (Lp.memLp g)).toLp (fun point => f point * g point)
lemma mulLp_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLp μ f g =ᵐ[μ] fun x => f x * g x := MemLp.coeFn_toLp _
def mulLpLinear (f : Func X) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLp μ f
  map_add' g h := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (g+h),mulLp_ae μ f g,mulLp_ae μ f h,
      Lp.coeFn_add g h,Lp.coeFn_add (mulLp μ f g) (mulLp μ f h)] with x ha hb hc hd he
    simp only [ha,he,Pi.add_apply,hb,hc,hd]
    exact mul_add _ _ _
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (c • g),mulLp_ae μ f g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (mulLp μ f g)] with x ha hb hc hd
    simp only [RingHom.id_apply,ha,hd,Pi.smul_apply,hb,hc,smul_eq_mul]
    ring
lemma mulLp_norm_le (f : Func X) (g : Lp ℂ 2 μ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖mulLp μ f g‖ ≤ C * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulLp_ae μ f g] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)
def mulLpCLM (f : Func X) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulLpLinear μ f).mkContinuous (bound f) (fun g => mulLp_norm_le μ f g (norm_le_bound f))
lemma mulLpCLM_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLpCLM μ f g =ᵐ[μ] fun x => f x * g x := mulLp_ae μ f g
lemma mulLp_l2 (f g : Func X) : mulLpCLM μ f (l2 μ g) = l2 μ (f*g) := by
  apply Lp.ext
  filter_upwards [mulLpCLM_ae μ f (l2 μ g),l2_ae μ g,l2_ae μ (f*g)] with x hx hy hz
  rw [hx,hy,hz]; rfl
end EuclideanFiveColor.BoundedMeasurable
end

noncomputable section
open scoped ComplexConjugate IsMulCommutative
namespace EuclideanFiveColor.CommutingSpectral
variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* unitary (H →L[ℂ] H))
abbrev algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))).topologicalClosure
instance algebra_closed : IsClosed (algebra U : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
lemma adjoin_comm : IsMulCommutative (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · rintro _ ⟨element,rfl⟩
    infer_instance
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩ _
    change ((U left * U right : unitary _) : H →L[ℂ] H) = ((U right * U left : unitary _) : H →L[ℂ] H)
    rw [← map_mul,← map_mul,mul_comm]
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩ _
    change ((U left * (U right)⁻¹ : unitary _) : H →L[ℂ] H) = (((U right)⁻¹ * U left : unitary _) : H →L[ℂ] H)
    rw [← map_inv,← map_mul,← map_mul,mul_comm]
open scoped IsMulCommutative in
instance algebra_commRing : CommRing (algebra U) :=
  let := adjoin_comm U
  inferInstance
instance algebra_commCStar : CommCStarAlgebra (algebra U) where

def generator (g : G) : algebra U :=
  ⟨U g,StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g))⟩
@[simp] lemma generator_one : generator U 1 = 1 := by ext; simp [generator]
@[simp] lemma generator_mul (g h : G) : generator U (g*h) = generator U g * generator U h := by
  apply Subtype.ext; change (U (g*h) : H →L[ℂ] H) = (U g : H →L[ℂ] H) * U h
  rw [map_mul]; rfl
lemma generator_unitary (g : G) : generator U g ∈ unitary (algebra U) := by
  constructor <;> apply Subtype.ext
  · exact (U g).property.1
  · exact (U g).property.2
variable [TopologicalSpace G] [DiscreteTopology G]
abbrev Spectrum := WeakDual.characterSpace ℂ (algebra U)
def character (φ : Spectrum U) : PontryaginDual G where
  toFun g := ⟨gelfandStarTransform (algebra U) (generator U g) φ, by
    change gelfandStarTransform (algebra U) (generator U g) φ ∈ Metric.sphere (0:ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply CStarRing.norm_of_mem_unitary
    exact Unitary.map_mem ((ContinuousMap.evalStarAlgHom ℂ ℂ φ).comp
      (gelfandStarTransform (algebra U)).toStarAlgHom) (generator_unitary U g)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change _ = (gelfandStarTransform (algebra U) (generator U g) φ) *
      (gelfandStarTransform (algebra U) (generator U h) φ)
    simp
  continuous_toFun := continuous_of_discreteTopology
lemma character_apply (φ : Spectrum U) (g : G) :
    (character U φ g : ℂ) = gelfandStarTransform (algebra U) (generator U g) φ := rfl
lemma character_continuous : Continuous (character U) := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi; intro g
  exact Continuous.subtype_mk (map_continuous (gelfandStarTransform (algebra U) (generator U g))) _
def calculus : C(PontryaginDual G,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (algebra U).subtype.comp <| (gelfandStarTransform (algebra U)).symm.toStarAlgHom.comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨character U,character_continuous U⟩)
def evaluation (g : G) : C(PontryaginDual G,ℂ) :=
  ⟨fun d => (d g : ℂ),continuous_subtype_val.comp ((continuous_apply g).comp ContinuousMonoidHom.isClosedEmbedding_coe.continuous)⟩
lemma calculus_evaluation (g : G) : calculus U (evaluation g) = U g := by
  change ((gelfandStarTransform (algebra U)).symm ((evaluation g).comp ⟨character U,character_continuous U⟩) : H →L[ℂ] H) = U g
  have he : (evaluation g).comp ⟨character U,character_continuous U⟩ =
      gelfandStarTransform (algebra U) (generator U g) := by ext φ; rfl
  rw [he,StarAlgEquiv.symm_apply_apply]; rfl
end EuclideanFiveColor.CommutingSpectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
open BoundedMeasurable
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def boundedCM (f : C(X,ℂ)) : Func X :=
  ⟨f,f.continuous.measurable,‖f‖₊,fun x => ContinuousMap.norm_coe_le_norm f x⟩
omit [T2Space X] in
@[simp] lemma boundedCM_apply (f : C(X,ℂ)) (x : X) : boundedCM f x = f x := rfl
omit [T2Space X] in
lemma boundedCM_toLp (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℂ)) :
    l2 μ (boundedCM f) = ContinuousMap.toLp 2 μ ℂ f := by
  apply Lp.ext
  exact (l2_ae μ _).trans (ContinuousMap.coeFn_toLp (μ := μ) (p := 2) (𝕜 := ℂ) f).symm
lemma mulCM_toLp (f g : C(X,ℂ)) :
    mulLpCLM (measure Φ v) (boundedCM f) (ContinuousMap.toLp 2 (measure Φ v) ℂ g) =
      ContinuousMap.toLp 2 (measure Φ v) ℂ (f*g) := by
  rw [← boundedCM_toLp,← boundedCM_toLp,mulLp_l2]
  congr 1
lemma cyclicMap_mul (f : C(X,ℂ)) (g : Lp ℂ 2 (measure Φ v)) :
    cyclicMap Φ v (mulLpCLM (measure Φ v) (boundedCM f) g) = Φ f (cyclicMap Φ v g) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) g
  obtain ⟨h,rfl⟩ := hy
  rw [mulCM_toLp,cyclicMap_toLp,cyclicMap_toLp,map_mul]
  rfl
lemma cyclicMap_one : cyclicMap Φ v (l2 (measure Φ v) (1:Func X)) = v := by
  have he : (1:Func X) = boundedCM (1:C(X,ℂ)) := rfl
  rw [he,boundedCM_toLp,cyclicMap_toLp,map_one]
  rfl
lemma cyclicMap_inner (f g : Lp ℂ 2 (measure Φ v)) :
    ⟪cyclicMap Φ v f,cyclicMap Φ v g⟫_ℂ = ⟪f,g⟫_ℂ :=
  (cyclicIsometry Φ v).inner_map_map f g
lemma cyclicMap_pair_one (f : Func X) :
    ⟪v,cyclicMap Φ v (l2 (measure Φ v) f)⟫_ℂ = ∫ x, f x ∂measure Φ v := by
  nth_rw 1 [← cyclicMap_one Φ v]
  rw [cyclicMap_inner,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae (measure Φ v) (1:Func X),l2_ae (measure Φ v) f] with x hx hy
  simp only [hx,hy,one_apply,RCLike.inner_apply,map_one,mul_one]
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.BoundedMeasurable
open EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H)
def ordinaryIndicator : Func D :=
  ⟨(C:Set D).indicator (fun _ => (1:ℂ)),measurable_const.indicator measurableSet_C,
    1,fun d => by by_cases hd : d ∈ C <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hd]⟩
lemma ordinaryIndicator_apply (d : D) : ordinaryIndicator d = (C:Set D).indicator (fun _ => (1:ℂ)) d := rfl
lemma ordinary_eval_continuous {d : D} (hd : d ∈ C) :
    Continuous (fun z : E => (eval z d : ℂ)) := by
  obtain ⟨ξ,rfl⟩ := hd
  change Continuous (fun z : E => (Circle.exp (inner ℝ (Multiplicative.toAdd ξ) (z:ℂ)) : ℂ))
  fun_prop
lemma ordinary_difference_tendsto (μ : Measure D) [IsFiniteMeasure μ] :
    Tendsto (fun z : E => ∫ d, ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2 ∂μ)
      (𝓝 0) (𝓝 0) := by
  have hm (z : E) : Measurable (fun d => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2) := by
    have he : Measurable (fun d : D => (eval z d : ℂ)) := (evaluation (G := DiscreteE) (Multiplicative.ofAdd z)).continuous.measurable
    exact ((he.sub measurable_const).mul (measurable ordinaryIndicator)).norm.pow_const 2
  have hb (z : E) (d : D) : ‖‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2‖ ≤ (4:ℝ) := by
    have hi : ‖ordinaryIndicator d‖ ≤ 1 := by
      by_cases hd : d ∈ C <;> simp [ordinaryIndicator_apply,hd]
    have he : ‖(eval z d : ℂ)-1‖ ≤ 2 := by
      calc
        _ ≤ ‖(eval z d : ℂ)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
    have hn : ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖ ≤ 2 := by
      rw [norm_mul]
      exact (mul_le_mul he hi (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [Real.norm_eq_abs,abs_sq]
    nlinarith [norm_nonneg (((eval z d:ℂ)-1)*ordinaryIndicator d)]
  have hl (d : D) : Tendsto (fun z : E => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2)
      (𝓝 0) (𝓝 (0:ℝ)) := by
    by_cases hd : d ∈ C
    · have he := ((ordinary_eval_continuous hd).tendsto (0:E)).sub_const (1:ℂ)
      have ht := (he.mul_const (ordinaryIndicator d)).norm.pow 2
      have hz : (eval (0:E) d : ℂ) = 1 := by
        change (d 1 : ℂ) = 1
        rw [map_one]; rfl
      simpa only [hz,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)] using ht
    · simp only [ordinaryIndicator_apply,Set.indicator_of_notMem hd,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ : D => (4:ℝ))
    (Filter.Eventually.of_forall (fun z : E => (hm z).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun z : E => Filter.Eventually.of_forall (hb z)))
    (integrable_const (4:ℝ)) (Filter.Eventually.of_forall hl)
  simpa only [integral_zero] using ht

def ordinaryVector : H := cyclicMap (calculus U) v (l2 (measure (calculus U) v) ordinaryIndicator)
lemma ordinaryVector_continuous : ordinaryVector U v ∈ ContinuousVectors.space U := by
  let μ := measure (calculus U) v
  have he (z : E) : ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v =
      cyclicMap (calculus U) v (l2 μ ((boundedCM (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))-1)*ordinaryIndicator)) := by
    dsimp [ordinaryVector,μ]
    rw [sub_mul,map_sub,one_mul,map_sub]
    rw [← mulLp_l2,cyclicMap_mul]
    rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)]
    rfl
  have hn (z : E) : ‖ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v‖^2 =
      ∫ d, ‖((eval z d:ℂ)-1)*ordinaryIndicator d‖^2 ∂μ := by
    rw [he]
    change ‖cyclicIsometry (calculus U) v _‖^2 = _
    rw [LinearIsometry.norm_map,norm_l2_sq]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.tendsto (0:ℝ) |>.comp (ordinary_difference_tendsto μ)
  simpa only [Function.comp_def,← hn,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht
lemma measure_ordinary_zero_of_orthogonal (hv : v ∈ (ContinuousVectors.space U)ᗮ) :
    measure (calculus U) v (C:Set D) = 0 := by
  have ho := (Submodule.mem_orthogonal' _ _).mp hv (ordinaryVector U v) (ordinaryVector_continuous U v)
  have hp := cyclicMap_pair_one (calculus U) v ordinaryIndicator
  change ⟪v,ordinaryVector U v⟫_ℂ = _ at hp
  rw [ho] at hp
  have hz : (measure (calculus U) v).real (C:Set D) = 0 := by
    have := congrArg Complex.re hp
    simpa only [ordinaryIndicator_apply,integral_indicator measurableSet_C,integral_const,
      Measure.restrict_apply_univ,Complex.real_smul, smul_eq_mul,mul_one,Complex.zero_re,Complex.ofReal_re,Measure.real] using this.symm
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma evaluation_one : evaluation (1:G) = 1 := by
  ext d
  change (d 1 : ℂ) = 1
  rw [map_one]; rfl
lemma evaluation_mul (g h : G) : evaluation (g*h) = evaluation g * evaluation h := by
  ext d
  change (d (g*h) : ℂ) = (d g : ℂ)*(d h : ℂ)
  rw [map_mul]; rfl
lemma star_evaluation (g : G) : star (evaluation g) = evaluation g⁻¹ := by
  ext d
  change star (d g : ℂ) = (d g⁻¹ : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (d g)).symm
@[simps] def evaluationHom : G →* C(PontryaginDual G,ℂ) where
  toFun := evaluation
  map_one' := evaluation_one
  map_mul' := evaluation_mul
lemma evaluation_span_dense : Dense (Submodule.span ℂ (Set.range (evaluation (G := G))) : Set C(PontryaginDual G,ℂ)) := by
  let A := StarAlgebra.adjoin ℂ (Set.range (evaluation (G := G)))
  have hs : star (Set.range (evaluation (G := G))) = Set.range (evaluation (G := G)) := by
    ext f
    rw [Set.mem_star]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← star_evaluation,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(star_evaluation g).symm⟩
  have he : A.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (evaluation (G := G))) := by
    rw [StarAlgebra.adjoin_eq_span,hs,Set.union_self]
    have hc : Submonoid.closure (Set.range (evaluation (G := G))) = MonoidHom.mrange (evaluationHom (G := G)) :=
      Submonoid.closure_eq (MonoidHom.mrange (evaluationHom (G := G)))
    rw [hc]
    rfl
  have hsep : A.SeparatesPoints := by
    intro d e hde
    have hn : ∃ g, d g ≠ e g := by
      by_contra! h
      exact hde (DFunLike.ext _ _ h)
    obtain ⟨g,hg⟩ := hn
    refine ⟨evaluation g,⟨evaluation g,StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g),rfl⟩,?_⟩
    change (d g : ℂ) ≠ (e g : ℂ)
    exact fun h => hg (Subtype.ext h)
  have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  rw [dense_iff_closure_eq,← he]
  change closure (A:Set C(PontryaginDual G,ℂ)) = _
  rw [← StarSubalgebra.topologicalClosure_coe,ht]
  rfl
end EuclideanFiveColor.CommutingSpectral
namespace EuclideanFiveColor.CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrableCM (f : C(X,ℂ)) : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def linear : C(X,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (integrableCM μ f) (integrableCM μ g)
  map_smul' c f := integral_smul c f
lemma norm_le (f : C(X,ℂ)) : ‖linear μ f‖ ≤ μ.real Set.univ * ‖f‖ := by
  simpa only [linear,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
def clm : C(X,ℂ) →L[ℂ] ℂ := (linear μ).mkContinuous (μ.real Set.univ) (norm_le μ)
lemma apply_clm (f : C(X,ℂ)) : clm μ f = ∫ x, f x ∂μ := rfl
end EuclideanFiveColor.CompactIntegral
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
lemma measure_eq_of_fourier (μ ν : Measure (PontryaginDual G)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (h : ∀ g, ∫ d, (d g : ℂ) ∂μ = ∫ d, (d g : ℂ) ∂ν) : μ = ν := by
  have he : CompactIntegral.clm μ = CompactIntegral.clm ν := by
    apply ContinuousLinearMap.ext_on evaluation_span_dense
    rintro _ ⟨g,rfl⟩
    exact h g
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(PontryaginDual G,ℂ) := ⟨fun d => (f d : ℂ),by fun_prop⟩
  have hh := congrArg (fun L : C(PontryaginDual G,ℂ) →L[ℂ] ℂ => (L fc).re) he
  simpa only [CompactIntegral.apply_clm,fc,ContinuousMap.coe_mk,integral_complex_ofReal,Complex.ofReal_re] using hh
end EuclideanFiveColor.CommutingSpectral
end

end OAI
