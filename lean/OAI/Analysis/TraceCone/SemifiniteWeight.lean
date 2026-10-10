import OAI.Analysis.TraceCone.NormalWeight
import OAI.Analysis.TraceCone.StrongConvergence
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

/-!
# The faithful normal semifinite trace extension

The trace on the GNS weak closure is semifinite, faithful, and normal. The GNS
space is separable for a separable algebra, and the representation is
nondegenerate.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

/-- A finite-weight subelement of a positive operator in the GNS weak closure. -/
def finiteSubelement (T : Positive τ.traceWeakClosure) (e : τ.FiniteTraceContraction) :
    Positive τ.traceWeakClosure := Positive.conjugate (CFC.sqrt T.1) (τ.traceGNSPositive e.1)

lemma finiteSubelement_le (T : Positive τ.traceWeakClosure) (e : τ.FiniteTraceContraction) :
    τ.finiteSubelement T e ≤ T := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul
    (a := CFC.sqrt T.1) (b := (τ.traceGNSPositive e.1).1) (τ.traceGNSPositive e.1).2.isSelfAdjoint
  have hn : ‖(τ.traceGNSPositive e.1).1‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le τ.traceGNSRep e.1.1).trans e.2.2.le
  change star (CFC.sqrt T.1)*(τ.traceGNSPositive e.1).1*CFC.sqrt T.1 ≤ T.1
  calc
    _ ≤ ‖(τ.traceGNSPositive e.1).1‖ • (star (CFC.sqrt T.1) * CFC.sqrt T.1) := h
    _ = ‖(τ.traceGNSPositive e.1).1‖ • T.1 := by
      rw [(CFC.sqrt_nonneg T.1).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self T.1 T.2]
    _ ≤ 1 • T.1 := smul_le_smul_of_nonneg_right hn T.2
    _ = T.1 := one_smul ℝ T.1

lemma finiteSubelement_weight (T : Positive τ.traceWeakClosure) (e : τ.FiniteTraceContraction) :
    τ.traceNormalWeight (τ.finiteSubelement T e) =
      ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 T.1.1) := by
  let S : τ.traceWeakClosure := CFC.sqrt T.1
  have hS : star S = S := (CFC.sqrt_nonneg T.1).isSelfAdjoint.star_eq
  have hSS : S*S = T.1 := CFC.sqrt_mul_sqrt_self T.1 T.2
  have he : τ.traceGNSRep e.1.1 = star (τ.finiteRootAction e)*τ.finiteRootAction e := by
    rw [finiteRootAction,← map_star,← map_mul,
      (CFC.sqrt_nonneg e.1.1).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e.1.1 e.1.2]
  have hval : (τ.finiteSubelement T e).1.1 =
      star (τ.finiteRootAction e*S.1)*(τ.finiteRootAction e*S.1) := by
    change star S.1*τ.traceGNSRep e.1.1*S.1 = _
    simp only [he,star_mul,mul_assoc]
  change (⨆ f : τ.FiniteTraceContraction,
    ENNReal.ofReal (τ.traceVectorForm f.1 f.2.1 (τ.finiteSubelement T e).1.1)) = _
  rw [hval]
  simp_rw [τ.traceVectorForm_starMul]
  change (⨆ f : τ.FiniteTraceContraction,
    ENNReal.ofReal (‖τ.finiteRootAction e (S.1 (τ.traceVector f.1 f.2.1))‖ ^ 2)) = _
  have hsval : star S.1 = S.1 := congrArg Subtype.val hS
  simp_rw [τ.finiteRootAction_double _ e S,hsval]
  rw [τ.finiteRootAction_iSup_norm]
  have hT : T.1.1 = star S.1*S.1 := by
    rw [hsval]
    exact (congrArg Subtype.val hSS).symm
  conv_rhs => rw [hT,τ.traceVectorForm_starMul]

lemma normalTraceCandidate_semifinite : τ.IsSemifiniteTrace τ.normalTraceCandidate := by
  intro T
  apply le_antisymm
  · change τ.traceNormalWeight T ≤ _
    apply iSup_le
    intro e
    let b : {b : Positive τ.traceWeakClosure // b ≤ T ∧ τ.normalTraceCandidate b < ∞} :=
      ⟨τ.finiteSubelement T e,τ.finiteSubelement_le T e,by
        change τ.traceNormalWeight (τ.finiteSubelement T e) < ∞
        rw [τ.finiteSubelement_weight]
        exact ENNReal.ofReal_lt_top⟩
    calc
      ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 T.1.1) = τ.normalTraceCandidate b.1 :=
        (τ.finiteSubelement_weight T e).symm
      _ ≤ _ := le_iSup (fun b : {b : Positive τ.traceWeakClosure // b ≤ T ∧ τ.normalTraceCandidate b < ∞} =>
        τ.normalTraceCandidate b.1) b
  · exact iSup_le (fun b => τ.normalTraceCandidate.monotone b.2.1)

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma finiteRootAction_nonneg (e : τ.FiniteTraceContraction) : 0 ≤ τ.finiteRootAction e :=
  map_nonneg τ.traceGNSRep (CFC.sqrt_nonneg e.1.1)

lemma finiteRootAction_approximates (ξ : τ.TraceGNS) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : τ.FiniteTraceContraction, ‖ξ-τ.finiteRootAction e ξ‖ < ε := by
  by_cases hξ : ξ = 0
  · let e : τ.FiniteTraceContraction := ⟨Positive.zero,by rw [τ.map_zero]; exact ENNReal.zero_lt_top,by simp [Positive.zero]⟩
    exact ⟨e,by simpa [hξ] using hε⟩
  have hn : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have hthreshold : ENNReal.ofReal (‖ξ‖ ^ 2-ε^2) < ENNReal.ofReal (‖ξ‖ ^ 2) :=
    (ENNReal.ofReal_lt_ofReal_iff hn).mpr (sub_lt_self _ (sq_pos_of_pos hε))
  rw [← τ.finiteRootAction_iSup_norm ξ] at hthreshold
  obtain ⟨e,he⟩ := lt_iSup_iff.mp hthreshold
  have he' : ‖ξ‖ ^ 2-ε^2 < ‖τ.finiteRootAction e ξ‖ ^ 2 := (ENNReal.ofReal_lt_ofReal_iff'.mp he).1
  have herr := positive_contraction_error (τ.finiteRootAction e) (τ.finiteRootAction_nonneg e)
    (τ.finiteRootAction_norm_le e) ξ
  refine ⟨e,?_⟩
  nlinarith [norm_nonneg (ξ-τ.finiteRootAction e ξ)]

lemma traceGNSLambda_star_norm (x : τ.finiteSquareAlgebra) :
    ‖τ.traceGNSLambda (star x)‖ = ‖τ.traceGNSLambda x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [τ.traceGNSLambda_norm_sq,τ.traceGNSLambda_norm_sq]
  have he : Positive.starMul (star x : τ.finiteSquareAlgebra).1 = Positive.mulStar x.1 := by
    apply Subtype.ext
    change star (star x.1)*star x.1 = x.1*star x.1
    rw [star_star]
  rw [he,← τ.tracial]

/-- Right multiplication by finite roots approximates every algebraic GNS vector. -/
lemma finiteTraceVector_cyclic_approx (x : τ.finiteSquareAlgebra) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : τ.FiniteTraceContraction,
      ‖τ.traceGNSLambda x-τ.traceGNSRep x.1 (τ.traceVector e.1 e.2.1)‖ < ε := by
  obtain ⟨e,he⟩ := τ.finiteRootAction_approximates (τ.traceGNSLambda (star x)) ε hε
  refine ⟨e,?_⟩
  have heq : τ.finiteSquareLeftMul (CFC.sqrt e.1.1) (star x) =
      star (τ.finiteSquareLeftMul x.1 (τ.finiteTraceSqrt e.1 e.2.1)) := by
    apply Subtype.ext
    change CFC.sqrt e.1.1*star x.1 = star (x.1*CFC.sqrt e.1.1)
    rw [star_mul,(CFC.sqrt_nonneg e.1.1).isSelfAdjoint.star_eq]
  change ‖τ.traceGNSLambda (star x)-τ.traceGNSRep (CFC.sqrt e.1.1) (τ.traceGNSLambda (star x))‖ < ε at he
  rw [τ.traceGNSRep_covariance,heq,← map_sub,← star_sub,τ.traceGNSLambda_star_norm,map_sub] at he
  simpa only [traceVector,τ.traceGNSRep_covariance] using he

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma normalTraceCandidate_faithful (T : Positive τ.traceWeakClosure)
    (hT : τ.normalTraceCandidate T = 0) : T = Positive.zero := by
  let S : τ.traceWeakClosure := CFC.sqrt T.1
  have hS : star S = S := (CFC.sqrt_nonneg T.1).isSelfAdjoint.star_eq
  have hSS : S*S = T.1 := CFC.sqrt_mul_sqrt_self T.1 T.2
  have hz (x : A) (e : τ.FiniteTraceContraction) :
      S.1 (τ.traceGNSRep x (τ.traceVector e.1 e.2.1)) = 0 := by
    let X : τ.traceWeakClosure := ⟨τ.traceGNSRep x,τ.traceGNSRep_mem_weakClosure x⟩
    have hconj : τ.normalTraceCandidate (Positive.conjugate X T) = 0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ (‖X*star X‖₊ : ℝ≥0∞)*τ.normalTraceCandidate T := (τ.normalTraceCandidate.conjugate_le X T)
        _ = 0 := by rw [hT,mul_zero]
    have heq : Positive.conjugate X T = Positive.starMul (S*X) := by
      apply Subtype.ext
      change star X*T.1*X = star (S*X)*(S*X)
      rw [star_mul,hS,← hSS]
      simp only [mul_assoc]
    rw [heq] at hconj
    have hh : ENNReal.ofReal (‖(S.1*X.1) (τ.traceVector e.1 e.2.1)‖ ^ 2) ≤
        τ.normalTraceCandidate (Positive.starMul (S*X)) := by
      change _ ≤ τ.traceNormalWeight (Positive.starMul (S*X))
      rw [← τ.traceVectorForm_starMul]
      exact le_iSup (fun e : τ.FiniteTraceContraction => ENNReal.ofReal
        (τ.traceVectorForm e.1 e.2.1 (star (S.1*X.1)*(S.1*X.1)))) e
    rw [hconj] at hh
    have hn := ENNReal.ofReal_eq_zero.mp (le_antisymm hh bot_le)
    have hn' : ‖S.1 (τ.traceGNSRep x (τ.traceVector e.1 e.2.1))‖ = 0 := by
      change ‖S.1 (τ.traceGNSRep x (τ.traceVector e.1 e.2.1))‖ ^ 2 ≤ 0 at hn
      nlinarith [norm_nonneg (S.1 (τ.traceGNSRep x (τ.traceVector e.1 e.2.1)))]
    exact norm_eq_zero.mp hn'
  have hzero (x : τ.finiteSquareAlgebra) : S.1 (τ.traceGNSLambda x) = 0 := by
    have happ (n : ℕ) := τ.finiteTraceVector_cyclic_approx x (1/(n+1:ℝ)) (by positivity)
    choose e he using happ
    have ht : Tendsto (fun n => τ.traceGNSRep x.1 (τ.traceVector (e n).1 (e n).2.1))
        atTop (𝓝 (τ.traceGNSLambda x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact (he n).le
    have ht' := S.1.continuous.continuousAt.tendsto.comp ht
    have hh : Tendsto (fun n => S.1 (τ.traceGNSRep x.1 (τ.traceVector (e n).1 (e n).2.1))) atTop (𝓝 0) := by
      simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : τ.TraceGNS)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht' hh
  have hOp : S.1 = 0 := by
    ext ξ
    have heq : (fun ξ => S.1 ξ) = (fun _ : τ.TraceGNS => 0) :=
      τ.traceGNSLambda_dense.equalizer S.1.continuous continuous_const (funext hzero)
    exact congrFun heq ξ
  apply Subtype.ext
  change T.1 = 0
  rw [← hSS]
  have hs : S = 0 := Subtype.ext hOp
  rw [hs,zero_mul]

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification.ExtendedTrace
open TopologicalSpace
open scoped CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

/-- The order supremum in the weak closure is its strong monotone limit. -/
lemma traceWeakClosure_lub_strong (s : Set (Positive τ.traceWeakClosure))
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (a : Positive τ.traceWeakClosure) (hlub : IsLUB s a) :
    letI : Nonempty s := hne.to_subtype
    letI : IsDirectedOrder s := hdir.isDirectedOrder
    ∀ ξ, Tendsto (fun b : s => b.1.1.1 ξ) atTop (𝓝 (a.1.1 ξ)) := by
  let : Nonempty s := hne.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  let T : s → τ.TraceGNS →L[ℂ] τ.TraceGNS := fun b => b.1.1.1
  have hT : Monotone T := fun _ _ h => h
  have hp : ∀ b, 0 ≤ T b := fun b => b.1.2
  have ha : ∀ b, T b ≤ a.1.1 := fun b => hlub.1 b.2
  obtain ⟨S,hS⟩ := monotone_operator_strong_limit T hT hp a.1.1 ha
  have hSpos : 0 ≤ S := strong_limit_nonneg T S hS (Eventually.of_forall hp)
  have hSle : S ≤ a.1.1 := by
    apply sub_nonneg.mp
    apply strong_limit_nonneg (l := atTop) (fun b : s => a.1.1-T b) (a.1.1-S)
    · intro ξ
      exact tendsto_const_nhds.sub (hS ξ)
    · exact Eventually.of_forall (fun b => sub_nonneg.mpr (ha b))
  have hleS (b : s) : T b ≤ S := by
    apply sub_nonneg.mp
    apply strong_limit_nonneg (l := atTop) (fun c : s => T c-T b) (S-T b)
    · intro ξ
      exact (hS ξ).sub tendsto_const_nhds
    · exact (eventually_ge_atTop b).mono (fun c hc => sub_nonneg.mpr (hT hc))
  have hWOT : Tendsto (fun b => ContinuousLinearMapWOT.ofCLM (T b)) atTop
      (𝓝 (ContinuousLinearMapWOT.ofCLM S)) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    exact tendsto_const_nhds.inner (𝕜 := ℂ) (hS ξ)
  have hSmem : S ∈ τ.traceWeakClosure := by
    apply (weakClosure_mem _ S).mpr
    apply isClosed_closure.mem_of_tendsto hWOT
    exact Eventually.of_forall (fun b => (weakClosure_mem _ (T b)).mp b.1.1.2)
  let p : Positive τ.traceWeakClosure := ⟨⟨S,hSmem⟩,hSpos⟩
  have heq : a = p := by
    apply le_antisymm
    · apply hlub.2
      intro b hb
      exact hleS ⟨b,hb⟩
    · exact hSle
  intro ξ
  rw [heq]
  exact hS ξ

lemma normalTraceCandidate_normal : τ.IsNormalTrace τ.normalTraceCandidate := by
  intro s hne hdir a hlub
  let : Nonempty s := hne.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  have ht := τ.traceWeakClosure_lub_strong s hne hdir a hlub
  apply le_antisymm
  · change τ.traceNormalWeight a ≤ _
    apply iSup_le
    intro e
    have ht' : Tendsto (fun b : s => ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 b.1.1.1)) atTop
        (𝓝 (ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 a.1.1))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      apply Complex.continuous_re.continuousAt.tendsto.comp
      exact tendsto_const_nhds.inner (𝕜 := ℂ) (ht (τ.traceVector e.1 e.2.1))
    apply le_of_tendsto ht'
    apply Eventually.of_forall
    intro b
    calc
      ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 b.1.1.1) ≤ τ.normalTraceCandidate b.1 :=
        le_iSup (fun e : τ.FiniteTraceContraction =>
          ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 b.1.1.1)) e
      _ ≤ ⨆ b : s, τ.normalTraceCandidate b.1 :=
        le_iSup (fun b : s => τ.normalTraceCandidate b.1) b
  · apply iSup_le
    intro b
    exact τ.normalTraceCandidate.monotone (hlub.1 b.2)

/-- The faithful normal semifinite extension of the trace to its GNS weak closure. -/
theorem trace_normal_extension (τ : ExtendedTrace A) :
    ∃ w : ExtendedTrace τ.traceWeakClosure,
      τ.IsNormalTrace w ∧ τ.IsSemifiniteTrace w ∧
      (∀ a, w a = 0 → a = Positive.zero) ∧
      (∀ a : Positive A, a.1 ∈ τ.finiteIdeal → w (τ.traceGNSPositive a) = τ a) := by
  exact ⟨τ.normalTraceCandidate,τ.normalTraceCandidate_normal,
    τ.normalTraceCandidate_semifinite,τ.normalTraceCandidate_faithful,τ.traceNormalWeight_rep_eq⟩

end TraceConeClassification.ExtendedTrace

namespace TraceConeClassification.ExtendedTrace
open TopologicalSpace
open scoped CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma finite_cyclic_root_dist (x : τ.finiteSquareAlgebra) (e f : τ.FiniteTraceContraction) :
    dist (τ.traceGNSRep x.1 (τ.traceVector e.1 e.2.1))
      (τ.traceGNSRep x.1 (τ.traceVector f.1 f.2.1)) =
    dist (τ.finiteRootAction e (τ.traceGNSLambda (star x)))
      (τ.finiteRootAction f (τ.traceGNSLambda (star x))) := by
  have heq (e : τ.FiniteTraceContraction) :
      τ.finiteSquareLeftMul (CFC.sqrt e.1.1) (star x) =
      star (τ.finiteSquareLeftMul x.1 (τ.finiteTraceSqrt e.1 e.2.1)) := by
    apply Subtype.ext
    change CFC.sqrt e.1.1*star x.1 = star (x.1*CFC.sqrt e.1.1)
    rw [star_mul,(CFC.sqrt_nonneg e.1.1).isSelfAdjoint.star_eq]
  simp only [dist_eq_norm,finiteRootAction,traceVector,τ.traceGNSRep_covariance,
    heq,← map_sub,← star_sub,τ.traceGNSLambda_star_norm]

lemma finite_cyclic_continuous (x : τ.finiteSquareAlgebra) :
    Continuous (fun e : τ.FiniteTraceContraction =>
      τ.traceGNSRep x.1 (τ.traceVector e.1 e.2.1)) := by
  have hs : Continuous (fun e : τ.FiniteTraceContraction => CFC.sqrt e.1.1) :=
    CFC.continuousOn_sqrt.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun e => e.1.2)
  have hc : Continuous (fun e : τ.FiniteTraceContraction =>
      τ.finiteRootAction e (τ.traceGNSLambda (star x))) := by
    exact ((map_continuous τ.traceGNSRep).comp hs).clm_apply continuous_const
  apply continuous_iff_continuousAt.mpr
  intro e
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [τ.finite_cyclic_root_dist]
  exact tendsto_iff_dist_tendsto_zero.mp hc.continuousAt

/-- The GNS representation of an extended trace on a separable algebra is separably acting. -/
theorem traceGNS_separable [SeparableSpace A] (τ : ExtendedTrace A) :
    SeparableSpace τ.TraceGNS := by
  let : Nonempty τ.FiniteTraceContraction :=
    ⟨⟨Positive.zero,by rw [τ.map_zero]; exact ENNReal.zero_lt_top,by simp [Positive.zero]⟩⟩
  let e : ℕ → τ.FiniteTraceContraction := denseSeq τ.FiniteTraceContraction
  have he : DenseRange e := denseRange_denseSeq _
  let s : Set τ.TraceGNS := ⋃ n, Set.range (fun a : A =>
    τ.traceGNSRep a (τ.traceVector (e n).1 (e n).2.1))
  have hs : TopologicalSpace.IsSeparable s := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro n
    apply TopologicalSpace.isSeparable_range
    exact (map_continuous τ.traceGNSRep).clm_apply continuous_const
  have hmem (x : τ.finiteSquareAlgebra) (f : τ.FiniteTraceContraction) :
      τ.traceGNSRep x.1 (τ.traceVector f.1 f.2.1) ∈ closure s := by
    have hh := mem_closure_image (τ.finite_cyclic_continuous x).continuousAt (he f)
    apply closure_mono _ hh
    rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
    exact Set.mem_iUnion.mpr ⟨n,⟨x.1,rfl⟩⟩
  have hLambda (x : τ.finiteSquareAlgebra) : τ.traceGNSLambda x ∈ closure s := by
    have happ (n : ℕ) := τ.finiteTraceVector_cyclic_approx x (1/(n+1:ℝ)) (by positivity)
    choose f hf using happ
    have ht : Tendsto (fun n => τ.traceGNSRep x.1 (τ.traceVector (f n).1 (f n).2.1))
        atTop (𝓝 (τ.traceGNSLambda x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact (hf n).le
    exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall (fun n => hmem x (f n)))
  have hd : Dense s := by
    intro ξ
    exact closure_minimal (by rintro _ ⟨x,rfl⟩; exact hLambda x) isClosed_closure
      (τ.traceGNSLambda_dense ξ)
  exact hd.isSeparable_iff.mp hs

end TraceConeClassification.ExtendedTrace

namespace TraceConeClassification.ExtendedTrace
open scoped CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma traceGNS_approximateUnit_strong (ξ : τ.TraceGNS) :
    Tendsto (fun a : A => τ.traceGNSRep a ξ) (CStarAlgebra.approximateUnit A) (𝓝 ξ) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨e,he⟩ := τ.finiteRootAction_approximates ξ (ε/4) (by positivity)
  let ζ := τ.finiteRootAction e ξ
  have he' : dist ξ ζ < ε/4 := by simpa only [dist_eq_norm] using he
  have ht : Tendsto (fun a : A => τ.traceGNSRep a ζ)
      (CStarAlgebra.approximateUnit A) (𝓝 ζ) := by
    have hh := (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_right (CFC.sqrt e.1.1)
    have hπ : Tendsto (fun a : A => τ.traceGNSRep (a * CFC.sqrt e.1.1))
        (CStarAlgebra.approximateUnit A) (𝓝 (τ.traceGNSRep (CFC.sqrt e.1.1))) :=
      ((map_continuous τ.traceGNSRep).tendsto _).comp hh
    have hc : Continuous (fun T : τ.TraceGNS →L[ℂ] τ.TraceGNS => T ξ) :=
      continuous_id.clm_apply continuous_const
    have hv := (hc.tendsto _).comp hπ
    simpa only [Function.comp_def, ζ, finiteRootAction, map_mul,mul_apply_eq_comp] using hv
  filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_norm,
    (Metric.tendsto_nhds.mp ht) (ε/2) (by positivity)] with a ha hah
  have hnorm : ‖τ.traceGNSRep a‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le _ _).trans ha
  have hdist : dist (τ.traceGNSRep a ξ) (τ.traceGNSRep a ζ) ≤ dist ξ ζ := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact ((τ.traceGNSRep a).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hh := dist_triangle (τ.traceGNSRep a ξ) (τ.traceGNSRep a ζ) ξ
  have hh' := dist_triangle (τ.traceGNSRep a ζ) ζ ξ
  rw [dist_comm ζ ξ] at hh'
  linarith

lemma traceWeakClosure_one : (1 : τ.TraceGNS →L[ℂ] τ.TraceGNS) ∈ τ.traceWeakClosure := by
  have ht : Tendsto (fun a : A => ContinuousLinearMapWOT.ofCLM (τ.traceGNSRep a))
      (CStarAlgebra.approximateUnit A) (𝓝 (ContinuousLinearMapWOT.ofCLM 1)) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    exact tendsto_const_nhds.inner (𝕜 := ℂ) (τ.traceGNS_approximateUnit_strong ξ)
  apply (weakClosure_mem _ _).mpr
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall (fun a => subset_closure ⟨τ.traceGNSRep a, ⟨a,rfl⟩,rfl⟩)

end TraceConeClassification.ExtendedTrace

namespace TraceConeClassification.ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The weak closure of the GNS representation is a von Neumann algebra. -/
theorem traceGNS_vonNeumann (τ : ExtendedTrace A) :
    ∃ N : VonNeumannAlgebra τ.TraceGNS,
      (N : Set (τ.TraceGNS →L[ℂ] τ.TraceGNS)) = τ.traceWeakClosure := by
  classical
  let : (atTop : Filter (Finset τ.TraceGNS × ℕ)).NeBot := inferInstance
  let C := τ.traceWeakClosure.toStarSubalgebra τ.traceWeakClosure_one
  have hC : Set.centralizer (Set.centralizer (C : Set (τ.TraceGNS →L[ℂ] τ.TraceGNS))) =
      (C : Set (τ.TraceGNS →L[ℂ] τ.TraceGNS)) := by
    apply Set.Subset.antisymm _ Set.subset_centralizer_centralizer
    intro T hT
    obtain ⟨a,ha,ht⟩ := bicommutant_strong_net C T hT
    have hw : Tendsto (fun p => ContinuousLinearMapWOT.ofCLM (a p)) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro ξ η
      exact tendsto_const_nhds.inner (𝕜 := ℂ) (ht ξ)
    apply (weakClosure_mem _ _).mpr
    apply isClosed_closure.mem_of_tendsto hw
    exact Eventually.of_forall (fun p => (weakClosure_mem _ _).mp (ha p))
  exact ⟨⟨C,hC⟩,rfl⟩

end TraceConeClassification.ExtendedTrace

end

end OAI
