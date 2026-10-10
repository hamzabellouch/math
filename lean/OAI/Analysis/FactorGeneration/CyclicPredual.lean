import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.UniformSpace.UniformApproximation
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Name the existing operator-norm structure to keep the norm topology
explicit through the nested dual and submodule constructions. -/
instance algebraDualNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (StrongDual ℂ M.toStarSubalgebra) := inferInstance

def traceCyclicLinearIsometry : M.toStarSubalgebra →ₗᵢ[ℂ]
    (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) :=
  { (traceCyclicHom τ).toLinearMap with norm_map' := traceCyclicHom_norm τ }

def cyclicCoefficient (ξ η : traceCyclicSpace τ) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ (traceCyclicSpace τ) η).comp
    (traceCyclicLinearIsometry τ).toContinuousLinearMap)

@[simp] theorem cyclicCoefficient_apply (ξ η : traceCyclicSpace τ) (a : M.toStarSubalgebra) :
    cyclicCoefficient τ ξ η a=inner ℂ ξ (traceCyclicHom τ a η) := rfl

theorem cyclicCoefficient_norm_le (ξ η : traceCyclicSpace τ) :
    ‖cyclicCoefficient τ ξ η‖ ≤ ‖ξ‖*‖η‖ := by
  apply (cyclicCoefficient τ ξ η).opNorm_le_bound (M := ‖ξ‖*‖η‖) (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
  intro a
  calc
    ‖cyclicCoefficient τ ξ η a‖ ≤ ‖ξ‖*‖traceCyclicHom τ a η‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖*(‖traceCyclicHom τ a‖*‖η‖) :=
      mul_le_mul_of_nonneg_left ((traceCyclicHom τ a).le_opNorm η) (norm_nonneg _)
    _ = (‖ξ‖*‖η‖)*‖a‖ := by rw [traceCyclicHom_norm]; ring

theorem cyclicCoefficient_continuous :
    Continuous (fun p : traceCyclicSpace τ × traceCyclicSpace τ => cyclicCoefficient τ p.1 p.2) := by
  unfold cyclicCoefficient
  fun_prop

abbrev cyclicPredual : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range (fun p : traceCyclicSpace τ × traceCyclicSpace τ =>
    cyclicCoefficient τ p.1 p.2))).topologicalClosure

instance cyclicPredual_normed : NormedAddCommGroup (cyclicPredual τ) := inferInstance

instance cyclicPredual_normedSpace : NormedSpace ℂ (cyclicPredual τ) := inferInstance

instance cyclicPredual_complete : CompleteSpace (cyclicPredual τ) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range
    (fun p : traceCyclicSpace τ × traceCyclicSpace τ => cyclicCoefficient τ p.1 p.2))).topologicalClosure)

theorem cyclicCoefficient_mem (ξ η : traceCyclicSpace τ) :
    cyclicCoefficient τ ξ η ∈ cyclicPredual τ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(ξ,η),rfl⟩)

theorem cyclicPredual_separable [TopologicalSpace.SeparableSpace (traceCyclicSpace τ)] :
    TopologicalSpace.SeparableSpace (cyclicPredual τ) :=
  (TopologicalSpace.isSeparable_range (cyclicCoefficient_continuous τ)).span.closure.separableSpace

def cyclicPredualEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ (cyclicPredual τ) :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict (cyclicPredual τ)

@[simp] theorem cyclicPredualEvaluation_apply (a : M.toStarSubalgebra) (f : cyclicPredual τ) :
    cyclicPredualEvaluation τ a f=f.val a := rfl

theorem cyclicPredualEvaluation_norm_le (a : M.toStarSubalgebra) :
    ‖cyclicPredualEvaluation τ a‖ ≤ ‖a‖ := by
  apply (cyclicPredualEvaluation τ a).opNorm_le_bound (M := ‖a‖) (norm_nonneg a)
  intro f
  exact (f.val.le_opNorm a).trans_eq (mul_comm _ _)

theorem cyclicPredualEvaluation_norm (a : M.toStarSubalgebra) :
    ‖cyclicPredualEvaluation τ a‖=‖a‖ := by
  apply le_antisymm (cyclicPredualEvaluation_norm_le τ a)
  rw [← traceCyclicHom_norm τ a]
  apply (traceCyclicHom τ a).opNorm_le_bound
    (M := ‖cyclicPredualEvaluation τ a‖) (ContinuousLinearMap.opNorm_nonneg _)
  intro η
  let ξ := traceCyclicHom τ a η
  let f : cyclicPredual τ := ⟨cyclicCoefficient τ ξ η,cyclicCoefficient_mem τ ξ η⟩
  have h : ‖inner ℂ ξ ξ‖ ≤ ‖cyclicPredualEvaluation τ a‖*(‖ξ‖*‖η‖) :=
    ((cyclicPredualEvaluation τ a).le_opNorm f).trans
      (mul_le_mul_of_nonneg_left (cyclicCoefficient_norm_le τ ξ η) (norm_nonneg _))
  have hs : ‖inner ℂ ξ ξ‖=‖ξ‖^2 := by
    rw [inner_self_eq_norm_sq_to_K,norm_pow]
    simp
  rw [hs] at h
  change ‖ξ‖ ≤ ‖cyclicPredualEvaluation τ a‖*‖η‖
  by_cases hz : ‖ξ‖=0
  · rw [hz]; positivity
  · have hp : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

def cyclicPredualEvaluationIsometry : M.toStarSubalgebra →ₗᵢ[ℂ] StrongDual ℂ (cyclicPredual τ) where
  toFun := cyclicPredualEvaluation τ
  map_add' _ _ := by ext f; exact map_add f.val _ _
  map_smul' _ _ := by ext f; exact map_smul f.val _ _
  norm_map' := cyclicPredualEvaluation_norm τ

end

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def ballContinuousFunctionals (M : VonNeumannAlgebra H) (C : ℝ) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) where
  carrier := {f | Continuous (fun T : weakOperatorBall M C => f ⟨T.val.toCLM,T.property.1⟩)}
  zero_mem' := by exact continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.const_smul c

theorem ballContinuousFunctionals_isClosed (M : VonNeumannAlgebra H) (C : ℝ) :
    IsClosed (ballContinuousFunctionals M C : Set (StrongDual ℂ M.toStarSubalgebra)) := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  have hbound : Tendsto (fun n => ‖g-f n‖*(|C|+1)) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := g)).sub hfg).norm.mul_const (|C|+1))
  have hu : TendstoUniformly
      (fun n (T : weakOperatorBall M C) => f n ⟨T.val.toCLM,T.property.1⟩)
      (fun T : weakOperatorBall M C => g ⟨T.val.toCLM,T.property.1⟩) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hbound ε hε] with n hn
    intro T
    have hT : ‖T.val.toCLM‖ ≤ |C|+1 :=
      T.property.2.trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
    rw [dist_eq_norm]
    change ‖(g-f n) ⟨T.val.toCLM,T.property.1⟩‖ < ε
    have h := ((g-f n).le_opNorm ⟨T.val.toCLM,T.property.1⟩).trans
      (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
    have hnn : 0 ≤ ‖g-f n‖*(|C|+1) := mul_nonneg (norm_nonneg _) (by positivity)
    exact h.trans_lt (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hnn] using hn)
  exact hu.continuous (Eventually.of_forall hf).frequently

include τ in
 theorem cyclicPredual_le_ballContinuousFunctionals (C : ℝ) :
    cyclicPredual τ ≤ ballContinuousFunctionals M C := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro f ⟨⟨ξ,η⟩,rfl⟩
    change Continuous (fun T : weakOperatorBall M C => inner ℂ ξ.val (T.val η.val))
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val η.val ξ.val
  · exact ballContinuousFunctionals_isClosed M C

theorem cyclicPredual_ball_continuous (C : ℝ) (f : cyclicPredual τ) :
    Continuous (fun T : weakOperatorBall M C => f.val ⟨T.val.toCLM,T.property.1⟩) :=
  cyclicPredual_le_ballContinuousFunctionals τ C f.property

end

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

instance predualWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ (cyclicPredual τ)))

instance predualWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ (cyclicPredual τ))))

def predualWeakEvaluation : M.toStarSubalgebra →ₗ[ℂ] WeakDual ℂ (cyclicPredual τ) :=
  StrongDual.toWeakDual.toLinearMap.comp (cyclicPredualEvaluationIsometry τ).toLinearMap

def predualWeakBall (C : ℝ) : Set (WeakDual ℂ (cyclicPredual τ)) :=
  predualWeakEvaluation τ '' {a | ‖a‖ ≤ C}

theorem predualWeakBall_isCompact (C : ℝ) : IsCompact (predualWeakBall τ C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  let f : weakOperatorBall M C → WeakDual ℂ (cyclicPredual τ) :=
    fun T => predualWeakEvaluation τ ⟨T.val.toCLM,T.property.1⟩
  have hf : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro z
    exact cyclicPredual_ball_continuous τ C z
  have he : predualWeakBall τ C=Set.range f := by
    ext T
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩
  rw [he]
  exact isCompact_range hf

theorem predualWeakBall_convex (C : ℝ) : Convex ℝ (predualWeakBall τ C) := by
  have h : Convex ℝ {a : M.toStarSubalgebra | ‖a‖ ≤ C} := by
    simpa only [Metric.closedBall,dist_zero_right] using convex_closedBall (0 : M.toStarSubalgebra) C
  exact h.linear_image ((predualWeakEvaluation τ).restrictScalars ℝ)

theorem dual_norm_le_of_re_unitBall (f : StrongDual ℂ M.toStarSubalgebra) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a : M.toStarSubalgebra,‖a‖ ≤ 1 → (f a).re ≤ C) : ‖f‖ ≤ C := by
  let r : StrongDual ℝ M.toStarSubalgebra := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm f
  have hr : ‖r‖=‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm.norm_map f
  rw [← hr]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro a ha
  change |(f a).re| ≤ C
  apply abs_le.mpr
  refine ⟨?_,hf a ha.le⟩
  have hn := hf (-a) (by simpa only [norm_neg] using ha.le)
  simpa only [map_neg,Complex.neg_re,neg_le] using hn

private theorem weakDual_separation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set (WeakDual ℂ E)} {x : WeakDual ℂ E}
    (hs : Convex ℝ s) (hclosed : IsClosed s) (hx : x ∉ s) :
    ∃ (g : StrongDual ℂ (WeakDual ℂ E)) (u : ℝ),
      (∀ a ∈ s, (g a).re < u) ∧ u < (g x).re := by
  let : AddCommGroup (WeakDual ℂ E) := inferInstance
  let : Module ℝ (WeakDual ℂ E) := inferInstanceAs (Module ℝ (StrongDual ℂ E))
  let : Module ℂ (WeakDual ℂ E) := inferInstanceAs (Module ℂ (StrongDual ℂ E))
  let : IsScalarTower ℝ ℂ (WeakDual ℂ E) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ E))
  let : LocallyConvexSpace ℝ (WeakDual ℂ E) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ E)))
  exact RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hs hclosed hx

theorem cyclicPredualEvaluation_unitBall_surjective
    (φ : StrongDual ℂ (cyclicPredual τ)) (hφ : ‖φ‖ ≤ 1) :
    ∃ a : M.toStarSubalgebra,‖a‖ ≤ 1 ∧ cyclicPredualEvaluation τ a=φ := by
  have hm : StrongDual.toWeakDual φ ∈ predualWeakBall τ 1 := by
    by_contra hnot
    obtain ⟨g,u,hgu,hug⟩ := weakDual_separation
      (predualWeakBall_convex τ 1) (predualWeakBall_isCompact τ 1).isClosed hnot
    obtain ⟨f,hf⟩ := LinearMap.dualEmbedding_surjective
      (topDualPairing ℂ (cyclicPredual τ)) g
    have he (a : M.toStarSubalgebra) : g (predualWeakEvaluation τ a)=f.val a := by
      rw [← hf]
      rfl
    have heφ : g (StrongDual.toWeakDual φ)=φ f := by
      rw [← hf]
      rfl
    have hu : 0 < u := by
      have h := hgu (predualWeakEvaluation τ 0) ⟨0,by simp,rfl⟩
      simpa only [he,map_zero,Complex.zero_re] using h
    have hn : ‖f.val‖ ≤ u := dual_norm_le_of_re_unitBall f.val u hu.le (fun a ha => by
      have hh := (hgu (predualWeakEvaluation τ a) ⟨a,ha,rfl⟩).le
      rw [he] at hh
      exact hh)
    have hb : (φ f).re ≤ u := by
      calc
        (φ f).re ≤ ‖φ f‖ := Complex.re_le_norm _
        _ ≤ ‖φ‖*‖f‖ := φ.le_opNorm f
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg f)
        _ = ‖f‖ := one_mul _
        _ ≤ u := hn
    rw [heφ] at hug
    exact (not_lt_of_ge hb) hug
  obtain ⟨a,ha,he⟩ := hm
  exact ⟨a,ha,congrArg WeakDual.toStrongDual he⟩

end

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

instance functionalSubspaceNormed : NormedAddCommGroup F := inferInstance

instance functionalSubspaceNormedSpace : NormedSpace ℂ F := inferInstance

def functionalSubspaceEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ F :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict F

@[simp] theorem functionalSubspaceEvaluation_apply (a : M.toStarSubalgebra) (f : F) :
    functionalSubspaceEvaluation F a f = f.val a := rfl

def functionalSubspaceEvaluationLinear : M.toStarSubalgebra →ₗ[ℂ] StrongDual ℂ F where
  toFun := functionalSubspaceEvaluation F
  map_add' a b := by ext f; exact map_add f.val a b
  map_smul' c a := by ext f; exact map_smul f.val c a

instance functionalSubspaceWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ F) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ F))

instance functionalSubspaceWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ F) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ F)))

def functionalSubspaceWeakEvaluation : M.toStarSubalgebra →ₗ[ℂ] WeakDual ℂ F :=
  StrongDual.toWeakDual.toLinearMap.comp (functionalSubspaceEvaluationLinear F)

def functionalSubspaceWeakBall (C : ℝ) : Set (WeakDual ℂ F) :=
  functionalSubspaceWeakEvaluation F '' {a | ‖a‖ ≤ C}

theorem functionalSubspaceWeakBall_isCompact (C : ℝ)
    (hF : F ≤ ballContinuousFunctionals M C) : IsCompact (functionalSubspaceWeakBall F C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  let f : weakOperatorBall M C → WeakDual ℂ F :=
    fun T => functionalSubspaceWeakEvaluation F ⟨T.val.toCLM,T.property.1⟩
  have hf : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro z
    exact hF z.property
  have he : functionalSubspaceWeakBall F C=Set.range f := by
    ext T
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩
  rw [he]
  exact isCompact_range hf

theorem functionalSubspaceWeakBall_convex (C : ℝ) : Convex ℝ (functionalSubspaceWeakBall F C) := by
  have h : Convex ℝ {a : M.toStarSubalgebra | ‖a‖ ≤ C} := by
    simpa only [Metric.closedBall,dist_zero_right] using convex_closedBall (0 : M.toStarSubalgebra) C
  exact h.linear_image ((functionalSubspaceWeakEvaluation F).restrictScalars ℝ)

theorem functionalSubspaceEvaluation_unitBall_surjective
    (hF : F ≤ ballContinuousFunctionals M 1)
    (φ : StrongDual ℂ F) (hφ : ‖φ‖ ≤ 1) :
    ∃ a : M.toStarSubalgebra,‖a‖ ≤ 1 ∧ functionalSubspaceEvaluation F a=φ := by
  have hm : StrongDual.toWeakDual φ ∈ functionalSubspaceWeakBall F 1 := by
    by_contra hnot
    obtain ⟨g,u,hgu,hug⟩ := weakDual_separation
      (functionalSubspaceWeakBall_convex F 1) (functionalSubspaceWeakBall_isCompact F 1 hF).isClosed hnot
    obtain ⟨f,hf⟩ := LinearMap.dualEmbedding_surjective
      (topDualPairing ℂ F) g
    have he (a : M.toStarSubalgebra) : g (functionalSubspaceWeakEvaluation F a)=f.val a := by
      rw [← hf]
      rfl
    have heφ : g (StrongDual.toWeakDual φ)=φ f := by
      rw [← hf]
      rfl
    have hu : 0 < u := by
      have h := hgu (functionalSubspaceWeakEvaluation F 0) ⟨0,by simp,rfl⟩
      simpa only [he,map_zero,Complex.zero_re] using h
    have hn : ‖f.val‖ ≤ u := dual_norm_le_of_re_unitBall f.val u hu.le (fun a ha => by
      have hh := (hgu (functionalSubspaceWeakEvaluation F a) ⟨a,ha,rfl⟩).le
      rw [he] at hh
      exact hh)
    have hb : (φ f).re ≤ u := by
      calc
        (φ f).re ≤ ‖φ f‖ := Complex.re_le_norm _
        _ ≤ ‖φ‖*‖f‖ := φ.le_opNorm f
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg f)
        _ = ‖f‖ := one_mul _
        _ ≤ u := hn
    rw [heφ] at hug
    exact (not_lt_of_ge hb) hug
  obtain ⟨a,ha,he⟩ := hm
  exact ⟨a,ha,congrArg WeakDual.toStrongDual he⟩

/-- Unit-ball surjectivity extends by rescaling to the whole dual. -/
theorem functionalSubspaceEvaluation_surjective
    (hF : F ≤ ballContinuousFunctionals M 1) :
    Function.Surjective (functionalSubspaceEvaluation F) := by
  intro φ
  let c : ℂ := (‖φ‖ + 1 : ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast ne_of_gt (by positivity : 0 < ‖φ‖ + 1)
  have hnorm : ‖c⁻¹ • φ‖ ≤ 1 := by
    rw [norm_smul, norm_inv]
    have hn : ‖c‖ = ‖φ‖ + 1 := by
      dsimp [c]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖φ‖ + 1)).mpr (by linarith)
  obtain ⟨a, _, ha⟩ := functionalSubspaceEvaluation_unitBall_surjective F hF (c⁻¹ • φ) hnorm
  refine ⟨c • a, ?_⟩
  change functionalSubspaceEvaluationLinear F (c • a) = φ
  rw [map_smul]
  change c • functionalSubspaceEvaluation F a = φ
  rw [ha, smul_smul, mul_inv_cancel₀ hc, one_smul]

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ballContinuousFunctionals_eq_cyclicPredual :
    ballContinuousFunctionals M 1 = cyclicPredual τ := by
  apply le_antisymm
  · intro f hf
    let F := ballContinuousFunctionals M 1
    let K : Submodule ℂ F := (cyclicPredual τ).comap F.subtype
    let : IsClosed (K : Set F) :=
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
    let z : F := ⟨f, hf⟩
    by_contra hz
    have hq : K.mkQ z ≠ 0 := by
      intro heq
      exact hz ((Submodule.Quotient.mk_eq_zero K).mp heq)
    obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
    obtain ⟨a, ha⟩ := functionalSubspaceEvaluation_surjective F le_rfl (g.comp K.mkQL)
    have ha0 : a = 0 := by
      apply norm_eq_zero.mp
      rw [← cyclicPredualEvaluation_norm τ]
      apply norm_eq_zero.mpr
      ext q
      change q.val a = 0
      let q' : F := ⟨q.val, cyclicPredual_le_ballContinuousFunctionals τ 1 q.property⟩
      have hk : K.mkQ q' = 0 := (Submodule.Quotient.mk_eq_zero K).mpr q.property
      have h := congrArg (fun ψ : StrongDual ℂ F => ψ q') ha
      change q.val a = g (K.mkQ q') at h
      simpa only [hk, map_zero] using h
    apply hg
    have h := congrArg (fun ψ : StrongDual ℂ F => ψ z) ha
    change f a = g (K.mkQ z) at h
    simpa only [ha0, map_zero] using h.symm
  · exact cyclicPredual_le_ballContinuousFunctionals τ 1

theorem mem_cyclicPredual_iff_unitBall_continuous (f : StrongDual ℂ M.toStarSubalgebra) :
    f ∈ cyclicPredual τ ↔
      Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩) := by
  rw [← ballContinuousFunctionals_eq_cyclicPredual τ]
  rfl

theorem mem_cyclicPredual_of_unitBall_continuous (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩)) :
    f ∈ cyclicPredual τ :=
  (mem_cyclicPredual_iff_unitBall_continuous τ f).mpr hf

end Generator.Tracial

end

end OAI
