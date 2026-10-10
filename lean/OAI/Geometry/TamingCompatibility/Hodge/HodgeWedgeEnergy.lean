import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.GeometricCutoff
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameDifferential

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.MetricHodge
open MetricForms MetricModel ExteriorForms ContinuousAlternatingMap HodgeFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem full_wedge_energy (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) :
    pairing g (starThree g F (wedgeOne ξ (starTwo g J F a)))
      (starThree g F (wedgeOne ξ (starTwo g J F a))) +
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) *
        pairing g a a := by
  obtain ⟨b,hb,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis g J hJ horth hdim
  rw [pairing_one_eq_sum g hdim b hb,pairing_one_eq_sum g hdim b hb,
    pairing_one_eq_sum g hdim b hb,← coordinates_pairing g hdim b hb,
    real_inner_self_eq_norm_sq]
  have hf (i : Fin 4) : (ofSubsingletonLIE (0 : Fin 1) ξ) ![b i] = ξ (b i) := rfl
  simp_rw [hf]
  simp_rw [star_wedge_star_coordinate g hdim b hb J horth h0 h1 h2 h3 F hF,
    star_wedge_coordinate g hdim b hb J h0 h1 h2 h3 F hF]
  have he := UnitaryFrame.hodge_symbol_energy (WithLp.toLp 2 (fun i => ξ (b i))) (coordinates b a)
  simp only [EuclideanSpace.real_norm_sq_eq] at he ⊢
  simpa only [pow_two, Matrix.cons_val_zero,
    WithLp.ofLp_toLp] using he
end TamingCompatibility.MetricHodge

end
end

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
local instance (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

lemma hodgeStar_add (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) : starTwo J α ht (a+b) = starTwo J α ht a + starTwo J α ht b := by
  funext x
  ext v
  simp only [ManifoldHodge.starTwo,MetricHodge.starTwo,Pi.add_apply,
    MetricForms.pairing_add_left',ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply,ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,smul_eq_mul]
  ring

lemma hodgeStar_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (c : ℝ) (a : TwoForm X) : starTwo J α ht (c • a) = c • starTwo J α ht a := by
  funext x
  ext v
  simp only [ManifoldHodge.starTwo,MetricHodge.starTwo,Pi.smul_apply,
    MetricForms.pairing_smul_left,ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,smul_eq_mul]
  ring

lemma hodgeStar_pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) :
    pairing J α ht (starTwo J α ht a) b x = pairing J α ht a (starTwo J α ht b) x := by
  exact MetricHodge.starTwo_self_adjoint (pointMetric J α ht x) (J.endomorphism x : Space →L[ℝ] Space) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def preStar : PreL2 A J α hs ht true →ₗᵢ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨starTwo J α ht a.val,starTwo_smooth J α hs ht a.property⟩
  map_add' a b := Subtype.ext (hodgeStar_add J α ht a.val b.val)
  map_smul' c a := Subtype.ext (hodgeStar_smul J α ht c a.val)
  norm_map' a := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [preL2_norm_sq,preL2_norm_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      change pairing J α ht (starTwo J α ht a.val) (starTwo J α ht a.val) x = _
      rw [hodgeStar_pairing,starTwo_square])

lemma preStar_square (a : PreL2 A J α hs ht true) :
    preStar A J α hs ht (preStar A J α hs ht a) = a :=
  Subtype.ext (starTwo_square J α ht a.val)

def l2Star : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  ((smoothL2 A J α hs ht true).toContinuousLinearMap.comp
    (preStar A J α hs ht).toContinuousLinearMap).extend
      (smoothL2 A J α hs ht true).toContinuousLinearMap

@[simp] lemma l2Star_smooth (a : PreL2 A J α hs ht true) :
    l2Star A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true (preStar A J α hs ht a) := by
  exact ContinuousLinearMap.extend_eq _ (smoothL2_dense A J α hs ht true)
    (smoothL2 A J α hs ht true).isometry.isUniformInducing a

lemma l2Star_square (a : L2 A J α hs ht true) :
    l2Star A J α hs ht (l2Star A J α hs ht a) = a := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq ((l2Star A J α hs ht).continuous.comp (l2Star A J α hs ht).continuous) continuous_id) ?_
  intro b
  rw [l2Star_smooth,l2Star_smooth,preStar_square]

lemma l2Star_norm (a : L2 A J α hs ht true) : ‖l2Star A J α hs ht a‖ = ‖a‖ := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq (l2Star A J α hs ht).continuous.norm continuous_norm) ?_
  intro b
  rw [l2Star_smooth,(smoothL2 A J α hs ht true).norm_map,
    (preStar A J α hs ht).norm_map,(smoothL2 A J α hs ht true).norm_map]

lemma l2Star_inner (a b : L2 A J α hs ht true) :
    ⟪l2Star A J α hs ht a,l2Star A J α hs ht b⟫ = ⟪a,b⟫ := by
  let S : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
    ⟨(l2Star A J α hs ht).toLinearMap,l2Star_norm A J α hs ht⟩
  exact S.inner_map_map a b

lemma l2Star_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2Star A J α hs ht a,b⟫ = ⟪a,l2Star A J α hs ht b⟫ := by
  conv_lhs => rw [← l2Star_square A J α hs ht b]
  exact l2Star_inner A J α hs ht a (l2Star A J α hs ht b)
end GeometricHilbert
end TamingCompatibility

end
end

section
noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility
open ManifoldForms ManifoldHodge GeometricAdjoint
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
local instance (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

lemma hodgeStar_fun_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (f : X → ℝ) (a : TwoForm X) :
    starTwo J α ht (fun x => f x • a x) = fun x => f x • starTwo J α ht a x := by
  funext x
  exact congrFun (hodgeStar_smul J α ht (f x) a) x

lemma codifferential_fun_smul (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : Smooth a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    codifferential J α ht (fun x => f x • a x) =
      (fun x => f x • codifferential J α ht a x) -
        starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) := by
  unfold codifferential
  rw [hodgeStar_fun_smul,exteriorDerivative_fun_smul hf (starTwo_smooth J α hs ht ha),
    ManifoldHodge.starThree_add]
  funext x
  let d : MetricForms.Form Space 3 := exteriorDerivative (starTwo J α ht a) x
  let t : MetricForms.Form Space 1 := starThree J α ht
    (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  change -(MetricHodge.starThree g F (f x • d) + t) =
    f x • (-MetricHodge.starThree g F d) - t
  rw [MetricHodge.starThree_smul]
  module

lemma full_pairing_star_wedge (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : TwoForm X) (ξ : ManifoldForms.Form X 1) (x : X) :
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ (starTwo J α ht a)))
      (starThree J α ht (ManifoldForms.wedgeOne ξ (starTwo J α ht a))) x +
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ a))
      (starThree J α ht (ManifoldForms.wedgeOne ξ a)) x =
      pairing J α ht ξ ξ x * pairing J α ht a a x := by
  have he := MetricHodge.full_wedge_energy (pointMetric J α ht x)
    (J.endomorphism x : Space →L[ℝ] Space) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x) (by simp [Space])
    (invariantPart J α x) (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)
    (ExteriorForms.oneLinear (E := Space) (ξ x)) (a x)
  have hx : ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
      (ExteriorForms.oneLinear (E := Space) (ξ x)) = ξ x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply _
  rw [hx] at he
  exact he

lemma full_cutoff_delta_pointwise (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : Smooth a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (x : X) :
    pairing J α ht (codifferential J α ht (fun x => f x • a x))
      (codifferential J α ht (fun x => f x • a x)) x +
    pairing J α ht (codifferential J α ht (starTwo J α ht (fun x => f x • a x)))
      (codifferential J α ht (starTwo J α ht (fun x => f x • a x))) x ≤
      2*(f x)^2*(pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht a))
          (codifferential J α ht (starTwo J α ht a)) x) +
      2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x := by
  rw [hodgeStar_fun_smul,codifferential_fun_smul J α hs ht ha hf,
    codifferential_fun_smul J α hs ht (starTwo_smooth J α hs ht ha) hf,starTwo_square]
  let d : MetricForms.Form Space 1 := codifferential J α ht a x
  let ds : MetricForms.Form Space 1 := codifferential J α ht (starTwo J α ht a) x
  let t : MetricForms.Form Space 1 :=
    starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) x
  let u : MetricForms.Form Space 1 :=
    starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  have h₁ := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • d) t
  have h₂ := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • ds) u
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right] at h₁ h₂
  have he := full_pairing_star_wedge J α ht a (scalarDifferential f) x
  let g := pointMetric J α ht x
  change MetricForms.pairing g t t + MetricForms.pairing g u u = _ at he
  change MetricForms.pairing g (f x • d - t) (f x • d - t) +
    MetricForms.pairing g (f x • ds - u) (f x • ds - u) ≤
      2*(f x)^2*(MetricForms.pairing g d d+MetricForms.pairing g ds ds) +
        2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x
  calc
    _ ≤ (2*(f x*(f x*MetricForms.pairing g d d)) + 2*MetricForms.pairing g t t) +
        (2*(f x*(f x*MetricForms.pairing g ds ds)) + 2*MetricForms.pairing g u u) :=
      add_le_add h₁ h₂
    _ = 2*(f x)^2*(MetricForms.pairing g d d+MetricForms.pairing g ds ds) +
        2*(MetricForms.pairing g t t+MetricForms.pairing g u u) := by ring
    _ = _ := by rw [he]; ring
end TamingCompatibility

end
end

end
end

end OAI
