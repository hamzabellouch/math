import OAI.MeasureTheory.CompactFactors.AlgebraModels
import OAI.MeasureTheory.CompactFactors.Stationary

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
/-- Discrete additive notation for the actual multiplicative algebraic rotation group. -/
def Rot := Additive K deriving AddCommGroup
instance : TopologicalSpace Rot := ⊥
instance : DiscreteTopology Rot := ⟨rfl⟩
def rotMul (g : Rot) : K := Additive.toMul g
def mulRot (k : K) : Rot := Additive.ofMul k
@[simp] lemma rotMul_mulRot (k : K) : rotMul (mulRot k) = k := rfl
@[simp] lemma mulRot_rotMul (g : Rot) : mulRot (rotMul g) = g := rfl
instance rotAction (X : Type*) [MulAction K X] : AddAction Rot X where
  vadd g x := rotMul g • x
  zero_vadd x := one_smul K x
  add_vadd g h x := mul_smul (rotMul g) (rotMul h) x
@[simp] lemma rot_vadd {X : Type*} [MulAction K X] (g : Rot) (x : X) :
    g +ᵥ x = rotMul g • x := rfl
instance rotMeasurable {X : Type*} [MeasurableSpace X] [MulAction K X]
    [MeasurableConstSMul K X] : MeasurableConstVAdd Rot X where
  measurable_const_vadd g := measurable_const_smul (rotMul g)
instance rotInvariant {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [SMulInvariantMeasure K X μ] : VAddInvariantMeasure Rot X μ where
  measure_preimage_vadd g s _hs := measure_preimage_smul μ (rotMul g) s
instance rotErgodic {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [ErgodicSMul K X μ] : ErgodicVAdd Rot X μ where
  aeconst_of_forall_preimage_vadd_ae_eq hm he :=
    ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hm (fun k => he (mulRot k))
lemma rot_zsmul_surjective (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (EuclideanFiveColor.BoundedMeasurable.scaleHom (G := Rot) n) := by
  intro g
  obtain ⟨k,hk⟩ := K_pow_surjective n.natAbs (Int.natAbs_ne_zero.mpr hn) (rotMul g)
  rcases n with n | n
  · refine ⟨mulRot k, ?_⟩
    change Additive.ofMul (k^n) = g
    exact congrArg mulRot hk
  · refine ⟨mulRot k⁻¹, ?_⟩
    change Additive.ofMul (k⁻¹ ^ (Int.negSucc n)) = g
    have he : k⁻¹ ^ (Int.negSucc n) = k^(n+1) := by simp
    rw [he]
    exact congrArg mulRot hk
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral
variable (k : ℕ)
def Proper (ω : E → Fin k) : Prop := ∀ x y : E, ‖(x:ℂ)-(y:ℂ)‖ = 1 → ω x ≠ ω y
abbrev Space := {ω : E → Fin k // Proper k ω}
lemma closed_proper : IsClosed {ω : E → Fin k | Proper k ω} := by
  unfold Proper
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x:E) => isClosed_iInter fun (y:E) => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : E → Fin k => (ω x,ω y)) := (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Fin k × Fin k | p.1 ≠ p.2}).preimage hc
instance : CompactSpace (Space k) := isCompact_iff_compactSpace.mp (closed_proper k).isCompact
def trans (a : E) (ω : Space k) : Space k := ⟨fun x => ω.val (x+a),by
  intro x y h
  apply ω.property (x+a) (y+a)
  change ‖(x:ℂ)+(a:ℂ)-((y:ℂ)+(a:ℂ))‖ = 1
  simpa only [add_sub_add_right_eq_sub] using h⟩
def rotate (b : K) (ω : Space k) : Space k := ⟨fun x => ω.val (kCoeff b * x),by
  intro x y h
  apply ω.property (kCoeff b*x) (kCoeff b*y)
  change ‖(b.val:ℂ)*(x:ℂ)-(b.val:ℂ)*(y:ℂ)‖ = 1
  rw [← mul_sub,norm_mul,Circle.norm_coe,one_mul,h]⟩
@[simp] lemma trans_apply (a : E) (ω : Space k) (x : E) : (trans k a ω).val x = ω.val (x+a) := rfl
@[simp] lemma rotate_apply (b : K) (ω : Space k) (x : E) : (rotate k b ω).val x = ω.val (kCoeff b*x) := rfl
lemma trans_continuous (a : E) : Continuous (trans k a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x+a)).comp continuous_subtype_val
lemma rotate_continuous (b : K) : Continuous (rotate k b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b*x)).comp continuous_subtype_val
@[simp] lemma trans_zero (ω : Space k) : trans k 0 ω = ω := by apply Subtype.ext; funext x; simp
lemma trans_add (a b : E) (ω : Space k) : trans k a (trans k b ω) = trans k (a+b) ω := by apply Subtype.ext; funext x; simp [add_assoc]
@[simp] lemma rotate_one (ω : Space k) : rotate k 1 ω = ω := by
  apply Subtype.ext
  funext x
  have h1 : kCoeff 1 = 1 := rfl
  simp [h1]
lemma rotate_mul (a b : K) (ω : Space k) : rotate k a (rotate k b ω) = rotate k (a*b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a*b)*x)
  have he : kCoeff (a*b) = kCoeff a * kCoeff b := by rfl
  rw [he]; ring_nf
lemma covariance (a : E) (b : K) (ω : Space k) : trans k a (rotate k b ω) = rotate k b (trans k (kCoeff b*a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply,rotate_apply,mul_add]
def transHomeo (a : E) : Space k ≃ₜ Space k where
  toFun := trans k a
  invFun := trans k (-a)
  left_inv ω := by rw [trans_add,neg_add_cancel,trans_zero]
  right_inv ω := by rw [trans_add,add_neg_cancel,trans_zero]
  continuous_toFun := trans_continuous k a
  continuous_invFun := trans_continuous k (-a)
def rotateHomeo (b : K) : Space k ≃ₜ Space k where
  toFun := rotate k b
  invFun := rotate k b⁻¹
  left_inv ω := by rw [rotate_mul,inv_mul_cancel,rotate_one]
  right_inv ω := by rw [rotate_mul,mul_inv_cancel,rotate_one]
  continuous_toFun := rotate_continuous k b
  continuous_invFun := rotate_continuous k b⁻¹
abbrev Trans := Additive DiscreteE
def tr (a : Trans) : Space k → Space k := trans k (Multiplicative.toAdd (Additive.toMul a))
def ro (b : Rot) : Space k → Space k := rotate k (rotMul b)
def measure (ω : Space k) : Measure (Space k) := EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω
instance (ω : Space k) : IsProbabilityMeasure (measure k ω) := inferInstanceAs (IsProbabilityMeasure (EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω))
lemma trans_preserving (ω : Space k) (a : E) : MeasurePreserving (trans k a) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (transHomeo k a)
  intro f
  apply EuclideanFiveColor.StationaryMean.average_translation (tr k) (ro k) ω
    (fun a b x => trans_add k _ _ x) (fun b a => Additive.ofMul (Multiplicative.ofAdd (kCoeff (rotMul b)*Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance k _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f (trans_continuous k a)
lemma rotate_preserving (ω : Space k) (b : K) : MeasurePreserving (rotate k b) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (rotateHomeo k b)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_rotation (tr k) (ro k) ω
    (fun a b x => rotate_mul k _ _ x) (mulRot b) f (rotate_continuous k b)
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.Koopman
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
def isometry (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ s hs
  invFun := Lp.compMeasurePreserving s.symm (hs.symm s)
  left_inv v := by
    change Lp.compMeasurePreserving s.symm (hs.symm s) (Lp.compMeasurePreserving s hs v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s : X → X) ∘ s.symm = id := funext s.apply_symm_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
  right_inv v := by
    change Lp.compMeasurePreserving s hs (Lp.compMeasurePreserving s.symm (hs.symm s) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s.symm : X → X) ∘ s = id := funext s.symm_apply_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
def unitary (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm (isometry μ s hs)
lemma unitary_apply (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) (v : Lp ℂ 2 μ) :
    (unitary μ s hs : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v = Lp.compMeasurePreserving s hs v := rfl
lemma nonlinear_commute (s : X → X) (hs : MeasurePreserving s μ μ)
    {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0) (v : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving s hs (hF.compLp h0 v) = hF.compLp h0 (Lp.compMeasurePreserving s hs v) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (hF.compLp h0 v) hs,
    hs.quasiMeasurePreserving.ae (hF.coeFn_compLp h0 v),
    hF.coeFn_compLp h0 (Lp.compMeasurePreserving s hs v),Lp.coeFn_compMeasurePreserving v hs] with x h1 h2 h3 h4
  simp only [Function.comp_apply,h1,h2,h3,h4]
end EuclideanFiveColor.Koopman
end

noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
def op (a : A) : H →L[ℂ] H := U (Multiplicative.ofAdd a)
@[simp] lemma op_zero (v : H) : op U 0 v = v := by simp [op]
lemma op_add (a b : A) (v : H) : op U (a+b) v = op U a (op U b v) := by
  change ((U (Multiplicative.ofAdd a * Multiplicative.ofAdd b) : unitary _) : H →L[ℂ] H) v = _
  rw [map_mul]; rfl
lemma op_comm (a b : A) (v : H) : op U a (op U b v) = op U b (op U a v) := by
  rw [← op_add,← op_add,add_comm]
lemma norm_op (a : A) (v : H) : ‖op U a v‖ = ‖v‖ := Unitary.norm_map _ _
lemma dist_op (a : A) (v w : H) : dist (op U a v) (op U a w) = dist v w := by
  simp only [dist_eq_norm,← map_sub,norm_op]
variable [TopologicalSpace A]
def space : Submodule ℂ H where
  carrier := {v | Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Tendsto (fun a => op U a (v+w)) (𝓝 0) (𝓝 (v+w))
    simpa only [map_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    change Tendsto (fun a => op U a (c • v)) (𝓝 0) (𝓝 (c • v))
    simpa only [map_smul] using hv.const_smul c
lemma mem_space (v : H) : v ∈ space U ↔ Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v) := Iff.rfl
lemma isClosed_space : IsClosed (space U : Set H) := by
  apply isClosed_of_closure_subset
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hv (ε/4) (by positivity)
  have ht := Metric.tendsto_nhds.mp hw (ε/2) (by positivity)
  filter_upwards [ht] with a ha
  have he : dist (op U a v) v ≤ 2 * dist v w + dist (op U a w) w := by
    calc
      _ ≤ dist (op U a v) (op U a w) + dist (op U a w) v := dist_triangle _ _ _
      _ ≤ dist (op U a v) (op U a w) + (dist (op U a w) w + dist w v) :=
        by linarith [dist_triangle (op U a w) w v]
      _ = _ := by rw [dist_op,dist_comm w v]; ring
  linarith
instance : CompleteSpace (space U) := (isClosed_space U).completeSpace_coe
lemma op_mem (a : A) {v : H} (hv : v ∈ space U) : op U a v ∈ space U := by
  have ht := ((op U a).continuous.tendsto v).comp hv
  change Tendsto (fun z => op U z (op U a v)) (𝓝 0) (𝓝 (op U a v))
  simpa only [Function.comp_def,op_comm U a] using ht
variable [IsTopologicalAddGroup A]
lemma orbit_continuous {v : H} (hv : v ∈ space U) : Continuous (fun a => op U a v) := by
  rw [continuous_iff_continuousAt]
  intro a
  have ht0 : Tendsto (fun b : A => b-a) (𝓝 a) (𝓝 0) := by
    have hh := ((tendsto_id : Tendsto (fun b : A => b) (𝓝 a) (𝓝 a)).sub_const a)
    rw [sub_self] at hh
    exact hh
  have ht := (((op U a).continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun b => op U b v) (𝓝 a) (𝓝 (op U a v))
  convert ht using 1
  ext b
  change op U b v = op U a (op U (b-a) v)
  rw [← op_add]
  congr 1
  abel_nf
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
abbrev Hilbert := Lp ℂ 2 (measure k ω)
def translation (a : E) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (transHomeo k a).toMeasurableEquiv (trans_preserving k ω a)
def rotation (b : K) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (rotateHomeo k b).toMeasurableEquiv (rotate_preserving k ω b)
lemma translation_apply (a : E) (v : Hilbert k ω) :
    (translation k ω a : Hilbert k ω →L[ℂ] Hilbert k ω) v =
      Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) v := rfl
lemma rotation_apply (b : K) (v : Hilbert k ω) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) v =
      Lp.compMeasurePreserving (rotate k b) (rotate_preserving k ω b) v := rfl
def representation : DiscreteE →* unitary (Hilbert k ω →L[ℂ] Hilbert k ω) where
  toFun a := translation k ω (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans k 0) (trans_preserving k ω 0) v = v
    have he : trans k 0 = id := funext (trans_zero k)
    simp only [he,Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans k (Multiplicative.toAdd a+Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans k (Multiplicative.toAdd a)) _ (Lp.compMeasurePreserving (trans k (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans k c x) (add_comm _ _)).trans (trans_add k _ _ x).symm
lemma op_apply (a : E) (v : Hilbert k ω) : op (representation k ω) a v =
    Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) v := rfl
lemma rotation_covariance (b : K) (a : E) (v : Hilbert k ω) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (op (representation k ω) a v) =
      op (representation k ω) (kCoeff b*a) ((rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) v) := by
  simp only [rotation_apply,op_apply,← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance k a b x
end PlaneFiveColor.LabelModel
end

noncomputable section
open scoped InnerProductSpace
namespace EuclideanFiveColor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma projection_fixed_of_contraction (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (F : H → H) (hF : LipschitzWith 1 F) (hS : ∀ v ∈ S, F v ∈ S)
    (v : H) (hv : F v = v) : F (S.starProjection v) = S.starProjection v := by
  let p := S.starProjection v
  have hp : p ∈ S := S.starProjection_apply_mem v
  have hh : ‖v-F p‖ ≤ ‖v-p‖ := by
    simpa only [hv,NNReal.coe_one,one_mul,dist_eq_norm] using hF.dist_le_mul v p
  have ho : ⟪v-p,p-F p⟫_ℂ = 0 := S.starProjection_inner_eq_zero v _ (S.sub_mem hp (hS p hp))
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v-p) (p-F p) ho
  rw [sub_add_sub_cancel] at he
  have hz : ‖p-F p‖ = 0 := by nlinarith [norm_nonneg (v-p),norm_nonneg (p-F p),norm_nonneg (v-F p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace EuclideanFiveColor.ContinuousVectors
variable {A X : Type*} [AddCommGroup A] [TopologicalSpace A] [MeasurableSpace X]
  (μ : Measure X) (U : Multiplicative A →* unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
  (s : A → X → X) (hs : ∀ a, MeasurePreserving (s a) μ μ)
  (hU : ∀ a v, op U a v = Lp.compMeasurePreserving (s a) (hs a) v)
include hU
lemma nonlinear_mem {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0)
    {v : Lp ℂ 2 μ} (hv : v ∈ space U) : hF.compLp h0 v ∈ space U := by
  have ht := (hF.continuous_compLp h0).continuousAt.tendsto.comp hv
  change Tendsto (fun a => op U a (hF.compLp h0 v)) (𝓝 0) (𝓝 (hF.compLp h0 v))
  convert ht using 1
  funext a
  simp only [Function.comp_apply,hU,Koopman.nonlinear_commute]
omit hU
def clamp (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)
lemma clamp_lipschitz : LipschitzWith 1 clamp := by
  have hr : LipschitzWith 1 (fun z : ℂ => z.re) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,← Complex.sub_re] using Complex.abs_re_le_norm (a-b)
  change LipschitzWith 1 (fun z : ℂ => ((max 0 (min 1 z.re) : ℝ) : ℂ))
  simpa only [one_mul,Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp ((hr.const_min 1).const_max 0)
@[simp] lemma clamp_zero : clamp 0 = 0 := by simp [clamp]
lemma clamp_range (z : ℂ) : (clamp z).im = 0 ∧ 0 ≤ (clamp z).re ∧ (clamp z).re ≤ 1 := by
  change (0 : ℝ) = 0 ∧ 0 ≤ max 0 (min 1 z.re) ∧ max 0 (min 1 z.re) ≤ 1
  exact ⟨rfl,le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
lemma clamp_eq {z : ℂ} (hz : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) : clamp z = z := by
  rw [clamp,min_eq_right hz.2.2,max_eq_right hz.2.1]
  exact Complex.ext (by simp) (by simpa using hz.1.symm)
include hU
lemma projection_range (v : Lp ℂ 2 μ)
    (hv : ∀ᵐ x ∂μ, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) :
    ∀ᵐ x ∂μ, ((space U).starProjection v x).im = 0 ∧
      0 ≤ ((space U).starProjection v x).re ∧ ((space U).starProjection v x).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero v = v := by
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero v,hv] with x hx hvx
    exact hx.trans (clamp_eq hvx)
  have hp := projection_fixed_of_contraction (space U) (clamp_lipschitz.compLp clamp_zero)
    (clamp_lipschitz.lipschitzWith_compLp clamp_zero)
    (fun v hv => nonlinear_mem μ U s hs hU clamp_lipschitz clamp_zero hv) v he
  have hae := clamp_lipschitz.coeFn_compLp clamp_zero ((space U).starProjection v)
  rw [hp] at hae
  filter_upwards [hae] with x hx
  exact hx.symm ▸ clamp_range _
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A] [TopologicalSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
lemma covariance_mem (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    {v : H} (hv : v ∈ space U) : (W : H →L[ℂ] H) v ∈ space U := by
  have h0 : φ.symm 0 = 0 := by simpa only [hφ] using φ.symm_apply_apply 0
  have ht0 := φ.symm.continuous.tendsto 0
  rw [h0] at ht0
  have ht := ((W.val.continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun a => op U a ((W : H →L[ℂ] H) v)) (𝓝 0) (𝓝 ((W : H →L[ℂ] H) v))
  simpa only [Function.comp_def,hc,φ.apply_symm_apply] using ht
lemma projection_covariance_fixed (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    (v : H) (hv : (W : H →L[ℂ] H) v = v) :
    (W : H →L[ℂ] H) ((space U).starProjection v) = (space U).starProjection v := by
  exact projection_fixed_of_contraction (space U) (W : H →L[ℂ] H)
    (Unitary.linearIsometryEquiv W).lipschitz (fun w hw => covariance_mem U W φ hφ hc hw) v hv
lemma op_orthogonal (a : A) {v : H} (hv : v ∈ (space U)ᗮ) : op U a v ∈ (space U)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  have hh := hv (op U (-a) w) (op_mem U (-a) hw)
  have he := Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U (-a) w)
  change ⟪op U a v,op U a (op U (-a) w)⟫_ℂ = _ at he
  rw [← op_add,add_neg_cancel,op_zero] at he
  exact he.trans hh
lemma projection_coefficient (v : H) (a : A)
    (hb : ⟪v-(space U).starProjection v, op U a (v-(space U).starProjection v)⟫_ℂ = 0) :
    ⟪(space U).starProjection v,op U a ((space U).starProjection v)⟫_ℂ = ⟪v,op U a v⟫_ℂ := by
  let p := (space U).starProjection v
  let b := v-p
  have hp : p ∈ space U := (space U).starProjection_apply_mem v
  have hbmem : b ∈ (space U)ᗮ := (space U).sub_starProjection_mem_orthogonal v
  have h1 : ⟪b,op U a p⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).mp hbmem _ (op_mem U a hp)
  have h2 : ⟪p,op U a b⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp (op_orthogonal U a hbmem) _ hp
  have he : v = p+b := by dsimp [b]; abel
  change ⟪p,op U a p⟫_ℂ = ⟪v,op U a v⟫_ℂ
  rw [he,map_add,inner_add_left,inner_add_right,inner_add_right,h1,h2]
  change _ = _ + 0 + (0 + ⟪b,op U a b⟫_ℂ)
  rw [hb]; simp
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
instance : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
instance : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
lemma measure_univ : (measure Φ v).real Set.univ = ‖v‖^2 := by
  have he := integral_real Φ v (1:C(X,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,realCM_one,map_one,one_apply_eq_self] at he
  exact he.trans (inner_self_eq_norm_sq (𝕜 := ℂ) v)
end EuclideanFiveColor.VectorMeasure
end

end OAI
