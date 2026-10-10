import OAI.Analysis.TraceCone.GNS
import OAI.Analysis.TraceCone.StrongDensity
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# The weak closure of the trace representation

Finite trace vectors define positive functionals on the GNS weak closure. Their
supremum is additive, homogeneous, lower semicontinuous, and agrees with the
original trace on its finite ideal.

This is the trace representation construction in
*The trace cone classifies Razak–Jacelon stabilizations*.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

/-- The weak-operator closed star algebra of the square-integrable representation. -/
def traceWeakClosure := weakClosure (NonUnitalStarAlgHom.range τ.traceGNSRep)
instance traceWeakClosure_closed : IsClosed (τ.traceWeakClosure : Set (τ.TraceGNS →L[ℂ] τ.TraceGNS)) :=
  weakClosure_closed _

instance traceWeakClosure_starOrdered : StarOrderedRing τ.traceWeakClosure := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change z.1 + x.1 ≤ z.1 + y.1
    simpa only [add_comm] using add_le_add_left (show x.1 ≤ y.1 from h) z.1
  · intro x
    constructor
    · intro hx
      have hs : CFC.sqrt x.1 ∈ τ.traceWeakClosure := by
        rw [CFC.sqrt_eq_real_sqrt x.1 hx]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt x.2
      refine ⟨⟨CFC.sqrt x.1, hs⟩, ?_⟩
      apply Subtype.ext
      change x.1 = star (CFC.sqrt x.1) * CFC.sqrt x.1
      rw [(CFC.sqrt_nonneg x.1).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self x.1 hx]
    · rintro ⟨s,rfl⟩
      exact star_mul_self_nonneg s.1

lemma traceGNSRep_mem_weakClosure (a : A) : τ.traceGNSRep a ∈ τ.traceWeakClosure := by
  apply (weakClosure_mem _ _).mpr
  exact subset_closure ⟨τ.traceGNSRep a, ⟨a,rfl⟩,rfl⟩

/-- The represented image of a positive element in the GNS weak closure. -/
def traceGNSPositive (a : Positive A) : Positive τ.traceWeakClosure :=
  ⟨⟨τ.traceGNSRep a.1, τ.traceGNSRep_mem_weakClosure a.1⟩,
    map_nonneg τ.traceGNSRep a.2⟩

/-- Normality is preservation of every existing directed positive supremum. -/
def IsNormalTrace (w : ExtendedTrace τ.traceWeakClosure) : Prop :=
  ∀ (s : Set (Positive τ.traceWeakClosure)), s.Nonempty → DirectedOn (· ≤ ·) s →
    ∀ a, IsLUB s a → w a = ⨆ b : s, w b.1

/-- The usual semifiniteness condition, including boundary value infinity. -/
def IsSemifiniteTrace (w : ExtendedTrace τ.traceWeakClosure) : Prop :=
  ∀ a, w a = ⨆ b : { b : Positive τ.traceWeakClosure // b ≤ a ∧ w b < ∞ }, w b.1

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)
open scoped InnerProductSpace

lemma positive_starMul_sqrt (a : Positive A) : Positive.starMul (CFC.sqrt a.1) = a := by
  apply Subtype.ext
  simp only [Positive.starMul, (CFC.sqrt_nonneg a.1).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self a.1 a.2]

def finiteTraceSqrt (a : Positive A) (ha : τ a < ∞) : τ.finiteSquareAlgebra :=
  ⟨CFC.sqrt a.1, by
    change τ (Positive.starMul (CFC.sqrt a.1)) < ∞
    rwa [positive_starMul_sqrt]⟩

def traceVector (a : Positive A) (ha : τ a < ∞) : τ.TraceGNS :=
  τ.traceGNSLambda (τ.finiteTraceSqrt a ha)

lemma traceVector_norm_sq (a : Positive A) (ha : τ a < ∞) :
    ‖τ.traceVector a ha‖ ^ 2 = (τ a).toReal := by
  rw [traceVector, τ.traceGNSLambda_norm_sq]
  change (τ (Positive.starMul (CFC.sqrt a.1))).toReal = _
  rw [positive_starMul_sqrt]

/-- A finite-trace positive element defines a vector functional. -/
def traceVectorForm (a : Positive A) (ha : τ a < ∞)
    (T : τ.TraceGNS →L[ℂ] τ.TraceGNS) : ℝ :=
  (inner ℂ (τ.traceVector a ha) (T (τ.traceVector a ha))).re

lemma traceVectorForm_wot_continuous (a : Positive A) (ha : τ a < ∞) :
    Continuous (fun T : τ.TraceGNS →WOT[ℂ] τ.TraceGNS =>
      τ.traceVectorForm a ha (ContinuousLinearMapWOT.toCLM T)) :=
  Complex.continuous_re.comp
    (ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _)

lemma traceVectorForm_starMul (a : Positive A) (ha : τ a < ∞)
    (x : τ.TraceGNS →L[ℂ] τ.TraceGNS) :
    τ.traceVectorForm a ha (star x * x) = ‖x (τ.traceVector a ha)‖ ^ 2 := by
  exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right x _).symm

lemma traceVectorForm_rep_starMul (a : Positive A) (ha : τ a < ∞) (x : A) :
    τ.traceVectorForm a ha (τ.traceGNSRep (star x * x)) =
      (τ (Positive.conjugate (star x) a)).toReal := by
  rw [map_mul, map_star, τ.traceVectorForm_starMul]
  change ‖τ.traceGNSRep x (τ.traceGNSLambda (τ.finiteTraceSqrt a ha))‖ ^ 2 = _
  rw [τ.traceGNSRep_covariance, τ.traceGNSLambda_norm_sq, τ.tracial]
  congr 2
  apply Subtype.ext
  change (x * CFC.sqrt a.1) * star (x * CFC.sqrt a.1) =
    star (star x) * a.1 * star x
  simp only [star_mul, star_star, (CFC.sqrt_nonneg a.1).isSelfAdjoint.star_eq,
    mul_assoc, ← mul_assoc (CFC.sqrt a.1) (CFC.sqrt a.1), CFC.sqrt_mul_sqrt_self a.1 a.2]

lemma traceVectorForm_nonneg (a : Positive A) (ha : τ a < ∞)
    (T : τ.TraceGNS →L[ℂ] τ.TraceGNS) (hT : 0 ≤ T) : 0 ≤ τ.traceVectorForm a ha T := by
  have he : star (CFC.sqrt T) * CFC.sqrt T = T := by
    rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self T hT]
  rw [← he, τ.traceVectorForm_starMul]
  positivity

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

/-- Finite-weight positive strict contractions, with their operator order. -/
abbrev FiniteTraceContraction := {a : Positive A // τ a < ∞ ∧ ‖a.1‖ < 1}

lemma finite_cfc_nnreal {a : Positive A} (ha : τ a < ∞) (f : ℝ≥0 → ℝ≥0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 a.1)) (hf0 : f 0 = 0)
    (C : ℝ≥0) (hC : ∀ t ∈ quasispectrum ℝ≥0 a.1, f t ≤ C * t) :
    τ ⟨cfcₙ f a.1, cfcₙ_nonneg_of_predicate⟩ < ∞ := by
  have hle : cfcₙ f a.1 ≤ (C : ℝ) • a.1 := by
    have hh := cfcₙ_mono hC hf (by fun_prop) hf0 (by simp)
    change cfcₙ f a.1 ≤ cfcₙ (fun t : ℝ≥0 => C * id t) a.1 at hh
    rw [cfcₙ_const_mul C id a.1 (by fun_prop) rfl, cfcₙ_id ℝ≥0 a.1 a.2] at hh
    exact hh
  apply lt_of_le_of_lt (τ.monotone (show (⟨cfcₙ f a.1, cfcₙ_nonneg_of_predicate⟩ : Positive A) ≤ Positive.scale C a from hle))
  rw [τ.map_scale_all]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top ha

lemma finiteTraceContraction_directed : Directed (· ≤ ·)
    (fun a : τ.FiniteTraceContraction => a.1) := by
  let f : ℝ≥0 → ℝ≥0 := fun t => 1 - (1+t)⁻¹
  let g : ℝ≥0 → ℝ≥0 := fun t => t * (1-t)⁻¹
  have hgCont (a : τ.FiniteTraceContraction) :
      ContinuousOn g (quasispectrum ℝ≥0 a.1.1) := by
    have (t) (ht : t ∈ quasispectrum ℝ≥0 a.1.1) : 1-t ≠ 0 := by
      exact (tsub_pos_of_lt ((CStarAlgebra.le_nnnorm_of_mem_quasispectrum ht).trans_lt a.2.2)).ne'
    dsimp [g]
    fun_prop
  have hgFin (a : τ.FiniteTraceContraction) :
      τ ⟨cfcₙ g a.1.1, cfcₙ_nonneg_of_predicate⟩ < ∞ := by
    apply τ.finite_cfc_nnreal a.2.1 g (hgCont a) (by simp [g]) (1-‖a.1.1‖₊)⁻¹
    intro t ht
    dsimp [g]
    rw [mul_comm t]
    gcongr
    · exact tsub_pos_of_lt a.2.2
    · exact CStarAlgebra.le_nnnorm_of_mem_quasispectrum ht
  have hfg (a : τ.FiniteTraceContraction) : a.1.1 = cfcₙ f (cfcₙ g a.1.1) := by
    calc
      a.1.1 = cfcₙ (f ∘ g) a.1.1 := by
        conv_lhs => rw [← cfcₙ_id ℝ≥0 a.1.1 a.1.2]
        apply cfcₙ_congr
        apply Set.InvOn.one_sub_one_add_inv.1.eqOn.symm.mono
        intro t ht
        exact (CStarAlgebra.le_nnnorm_of_mem_quasispectrum ht).trans_lt a.2.2
      _ = _ := by
        rw [cfcₙ_comp f g a.1.1 ?_ (by simp [f]) (hgCont a) (by simp [g]) a.1.2]
        dsimp [f]
        fun_prop (disch := intro _ _; positivity)
  intro a b
  let d : Positive A := ⟨cfcₙ g a.1.1 + cfcₙ g b.1.1,
    add_nonneg cfcₙ_nonneg_of_predicate cfcₙ_nonneg_of_predicate⟩
  have hd : τ d < ∞ := by
    change τ (Positive.add ⟨cfcₙ g a.1.1,cfcₙ_nonneg_of_predicate⟩ ⟨cfcₙ g b.1.1,cfcₙ_nonneg_of_predicate⟩) < ∞
    rw [τ.map_add]
    exact ENNReal.add_lt_top.mpr ⟨hgFin a,hgFin b⟩
  have hfFin : τ ⟨cfcₙ f d.1,cfcₙ_nonneg_of_predicate⟩ < ∞ := by
    refine τ.finite_cfc_nnreal hd f (by
      dsimp [f]
      fun_prop (disch := intro _ _; positivity)) (by simp [f]) 1 ?_
    intro t _
    dsimp [f]
    rw [one_mul]
    have hprod : t * (1+t)⁻¹ = 1 - (1+t)⁻¹ := by
      simp [field, mul_tsub]
    rw [← hprod]
    exact mul_le_of_le_one_right' (inv_le_one_of_one_le₀ (by simp))
  refine ⟨⟨⟨cfcₙ f d.1,cfcₙ_nonneg_of_predicate⟩,
    hfFin,norm_cfcₙ_one_sub_one_add_inv_lt_one d.1⟩, ?_, ?_⟩
  · change a.1.1 ≤ cfcₙ f d.1
    rw [hfg a]
    exact CFC.monotoneOn_one_sub_one_add_inv cfcₙ_nonneg_of_predicate d.2
      (le_add_of_nonneg_right cfcₙ_nonneg_of_predicate)
  · change b.1.1 ≤ cfcₙ f d.1
    rw [hfg b]
    exact CFC.monotoneOn_one_sub_one_add_inv cfcₙ_nonneg_of_predicate d.2
      (le_add_of_nonneg_left cfcₙ_nonneg_of_predicate)

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma traceVectorForm_mono (a b : Positive A) (ha : τ a < ∞) (hb : τ b < ∞)
    (hab : a ≤ b) (T : τ.traceWeakClosure) (hT : 0 ≤ T) :
    τ.traceVectorForm a ha T.1 ≤ τ.traceVectorForm b hb T.1 := by
  let S := CFC.sqrt T.1
  have hS : S ∈ τ.traceWeakClosure := by
    dsimp [S]
    rw [CFC.sqrt_eq_real_sqrt T.1 hT]
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt T.2
  let ξ : Fin 2 → τ.TraceGNS := ![τ.traceVector a ha, τ.traceVector b hb]
  have happ (n : ℕ) : ∃ x : A, ∀ i, ‖τ.traceGNSRep x (ξ i)-S (ξ i)‖ < 1/(n+1:ℝ) := by
    obtain ⟨R,hR,_,he⟩ := weakClosure_selfadjoint_strong_density
      (NonUnitalStarAlgHom.range τ.traceGNSRep) S hS (CFC.sqrt_nonneg T.1).isSelfAdjoint
      2 ξ (1/(n+1:ℝ)) (by positivity)
    obtain ⟨x,rfl⟩ := hR
    exact ⟨x,he⟩
  choose x hx using happ
  have ht (i : Fin 2) : Tendsto (fun n => τ.traceGNSRep (x n) (ξ i)) atTop (𝓝 (S (ξ i))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hx n i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hle (n : ℕ) : ‖τ.traceGNSRep (x n) (ξ 0)‖ ^ 2 ≤
      ‖τ.traceGNSRep (x n) (ξ 1)‖ ^ 2 := by
    change ‖τ.traceGNSRep (x n) (τ.traceVector a ha)‖ ^ 2 ≤
      ‖τ.traceGNSRep (x n) (τ.traceVector b hb)‖ ^ 2
    rw [← τ.traceVectorForm_starMul, ← τ.traceVectorForm_starMul,
      ← map_star, ← map_mul, τ.traceVectorForm_rep_starMul, τ.traceVectorForm_rep_starMul]
    apply (ENNReal.toReal_le_toReal (τ.conjugate_finite _ a ha).ne
      (τ.conjugate_finite _ b hb).ne).mpr
    exact τ.monotone (show Positive.conjugate (star (x n)) a ≤ Positive.conjugate (star (x n)) b from
      star_left_conjugate_le_conjugate (show a.1 ≤ b.1 from hab) (star (x n)))
  have hlim : ‖S (ξ 0)‖ ^ 2 ≤ ‖S (ξ 1)‖ ^ 2 :=
    le_of_tendsto_of_tendsto ((ht 0).norm.pow 2) ((ht 1).norm.pow 2) (Eventually.of_forall hle)
  have he : star S * S = T.1 := by
    rw [(CFC.sqrt_nonneg T.1).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self T.1 hT]
  rw [← he,τ.traceVectorForm_starMul,τ.traceVectorForm_starMul]
  exact hlim

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)
open scoped InnerProductSpace

/-- The supremum of the finite-vector functionals over finite-trace strict contractions. -/
def traceNormalWeight (T : Positive τ.traceWeakClosure) : ℝ≥0∞ :=
  ⨆ a : τ.FiniteTraceContraction, ENNReal.ofReal (τ.traceVectorForm a.1 a.2.1 T.1.1)

lemma traceVectorForm_add (a : Positive A) (ha : τ a < ∞)
    (S T : τ.TraceGNS →L[ℂ] τ.TraceGNS) :
    τ.traceVectorForm a ha (S+T) = τ.traceVectorForm a ha S + τ.traceVectorForm a ha T := by
  simp [traceVectorForm,inner_add_right]

lemma traceVectorForm_smul (a : Positive A) (ha : τ a < ∞)
    (r : ℝ) (T : τ.TraceGNS →L[ℂ] τ.TraceGNS) :
    τ.traceVectorForm a ha (r • T) = r * τ.traceVectorForm a ha T := by
  simp [traceVectorForm,inner_smul_right_eq_smul]

lemma traceNormalWeight_zero : τ.traceNormalWeight Positive.zero = 0 := by
  simp [traceNormalWeight,Positive.zero,traceVectorForm]

lemma traceNormalWeight_add (S T : Positive τ.traceWeakClosure) :
    τ.traceNormalWeight (Positive.add S T) = τ.traceNormalWeight S + τ.traceNormalWeight T := by
  have hdir (a b : τ.FiniteTraceContraction) : ∃ c : τ.FiniteTraceContraction,
      ENNReal.ofReal (τ.traceVectorForm a.1 a.2.1 S.1.1) + ENNReal.ofReal (τ.traceVectorForm b.1 b.2.1 T.1.1) ≤
      ENNReal.ofReal (τ.traceVectorForm c.1 c.2.1 S.1.1) + ENNReal.ofReal (τ.traceVectorForm c.1 c.2.1 T.1.1) := by
    obtain ⟨c,hac,hbc⟩ := τ.finiteTraceContraction_directed a b
    exact ⟨c,add_le_add (ENNReal.ofReal_le_ofReal (τ.traceVectorForm_mono _ _ _ _ hac S.1 S.2))
      (ENNReal.ofReal_le_ofReal (τ.traceVectorForm_mono _ _ _ _ hbc T.1 T.2))⟩
  rw [traceNormalWeight,traceNormalWeight,traceNormalWeight,ENNReal.iSup_add_iSup hdir]
  congr 1
  funext a
  change ENNReal.ofReal (τ.traceVectorForm a.1 a.2.1 (S.1.1+T.1.1)) = _
  rw [τ.traceVectorForm_add,ENNReal.ofReal_add
    (τ.traceVectorForm_nonneg _ _ _ S.2) (τ.traceVectorForm_nonneg _ _ _ T.2)]

lemma traceNormalWeight_scale (r : ℝ≥0) (T : Positive τ.traceWeakClosure) :
    τ.traceNormalWeight (Positive.scale r T) = (r : ℝ≥0∞) * τ.traceNormalWeight T := by
  rw [traceNormalWeight,traceNormalWeight,ENNReal.mul_iSup]
  congr 1
  funext a
  change ENNReal.ofReal (τ.traceVectorForm a.1 a.2.1 ((r:ℝ) • T.1.1)) = _
  rw [τ.traceVectorForm_smul]
  erw [ENNReal.ofReal_mul r.2]
  simp

lemma traceVectorForm_positive_continuous (a : Positive A) (ha : τ a < ∞) :
    Continuous (fun T : Positive τ.traceWeakClosure => τ.traceVectorForm a ha T.1.1) := by
  have hv : Continuous (fun T : Positive τ.traceWeakClosure => T.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  change Continuous (fun T : Positive τ.traceWeakClosure =>
    (inner ℂ (τ.traceVector a ha) (T.1.1 (τ.traceVector a ha))).re)
  exact Complex.continuous_re.comp (continuous_const.inner (hv.clm_apply continuous_const))

lemma traceNormalWeight_lowerSemicontinuous : LowerSemicontinuous τ.traceNormalWeight :=
  lowerSemicontinuous_iSup (fun a : τ.FiniteTraceContraction =>
    (ENNReal.continuous_ofReal.comp (τ.traceVectorForm_positive_continuous a.1 a.2.1)).lowerSemicontinuous)

lemma traceNormalWeight_mono : Monotone τ.traceNormalWeight := by
  intro S T hST
  apply iSup_mono
  intro a
  apply ENNReal.ofReal_le_ofReal
  have hp := τ.traceVectorForm_nonneg a.1 a.2.1 (T.1.1-S.1.1) (sub_nonneg.mpr hST)
  have he : τ.traceVectorForm a.1 a.2.1 (T.1.1-S.1.1) =
      τ.traceVectorForm a.1 a.2.1 T.1.1-τ.traceVectorForm a.1 a.2.1 S.1.1 := by
    simp [traceVectorForm,inner_sub_right]
  rw [he] at hp
  linarith

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma traceVectorForm_rep_positive (a : Positive A) (ha : τ a < ∞) (b : Positive A) :
    ENNReal.ofReal (τ.traceVectorForm a ha (τ.traceGNSRep b.1)) =
      τ (Positive.conjugate (CFC.sqrt b.1) a) := by
  have he : star (CFC.sqrt b.1)*CFC.sqrt b.1 = b.1 := by
    rw [(CFC.sqrt_nonneg b.1).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self b.1 b.2]
  conv_lhs => rw [← he,τ.traceVectorForm_rep_starMul]
  rw [(CFC.sqrt_nonneg b.1).isSelfAdjoint.star_eq]
  exact ENNReal.ofReal_toReal (τ.conjugate_finite _ a ha).ne

lemma traceNormalWeight_rep_le (b : Positive A) :
    τ.traceNormalWeight (τ.traceGNSPositive b) ≤ τ b := by
  apply iSup_le
  intro a
  change ENNReal.ofReal (τ.traceVectorForm a.1 a.2.1 (τ.traceGNSRep b.1)) ≤ τ b
  rw [τ.traceVectorForm_rep_positive]
  have hle : Positive.conjugate (CFC.sqrt b.1) a.1 ≤ Positive.scale ‖a.1.1‖₊ b := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul (a := CFC.sqrt b.1) (b := a.1.1)
    change star (CFC.sqrt b.1) * a.1.1 * CFC.sqrt b.1 ≤ (‖a.1.1‖₊ : ℝ) • b.1
    simpa only [Positive.conjugate,Positive.scale,(CFC.sqrt_nonneg b.1).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self b.1 b.2,coe_nnnorm] using h
  calc
    τ (Positive.conjugate (CFC.sqrt b.1) a.1) ≤ τ (Positive.scale ‖a.1.1‖₊ b) := τ.monotone hle
    _ = (‖a.1.1‖₊ : ℝ≥0∞) * τ b := τ.map_scale_all _ _
    _ ≤ 1 * τ b := mul_le_mul_of_nonneg_right (by exact_mod_cast a.2.2.le) bot_le
    _ = τ b := one_mul _

/-- A finite resolvent contraction. The strictly positive denominator is retained
also at the endpoint zero of the nonunital spectrum. -/
def finiteResolvent (a : Positive A) (ha : τ a < ∞) (r : ℝ≥0) (hr : 0 < r) :
    τ.FiniteTraceContraction := by
  let f : ℝ≥0 → ℝ≥0 := fun t => t/(r+t)
  have hc : Continuous f := by
    dsimp [f]
    fun_prop (disch := intro t; exact (add_pos_of_pos_of_nonneg hr t.2).ne')
  refine ⟨⟨cfcₙ f a.1,cfcₙ_nonneg_of_predicate⟩,?_,?_⟩
  · apply τ.finite_cfc_nnreal ha f hc.continuousOn (by simp [f]) r⁻¹
    intro t _
    dsimp [f]
    rw [div_eq_mul_inv,mul_comm t]
    gcongr
    exact le_add_of_nonneg_right t.2
  · have hn : ‖cfcₙ f a.1‖₊ < 1 := nnnorm_cfcₙ_nnreal_lt (fun t _ =>
      (div_lt_one (add_pos_of_pos_of_nonneg hr t.2)).mpr (lt_add_of_pos_left t hr))
    exact_mod_cast hn

lemma finiteResolvent_val (a : Positive A) (ha : τ a < ∞) (r : ℝ≥0) (hr : 0 < r) :
    (τ.finiteResolvent a ha r hr).1.1 = cfcₙ (fun t : ℝ≥0 => t/(r+t)) a.1 := rfl

lemma finiteResolvent_conjugate (a : Positive A) (ha : τ a < ∞) (r : ℝ≥0) (hr : 0 < r) :
    (Positive.conjugate (CFC.sqrt a.1) (τ.finiteResolvent a ha r hr).1).1 =
      cfcₙ (fun t : ℝ≥0 => t*(t/(r+t))) a.1 := by
  have hc : Continuous (fun t : ℝ≥0 => t/(r+t)) := by
    fun_prop (disch := intro t; exact (add_pos_of_pos_of_nonneg hr t.2).ne')
  change star (CFC.sqrt a.1) * cfcₙ (fun t : ℝ≥0 => t/(r+t)) a.1 * CFC.sqrt a.1 = _
  rw [(CFC.sqrt_nonneg a.1).isSelfAdjoint.star_eq,CFC.sqrt,
    ← cfcₙ_mul NNReal.sqrt (fun t : ℝ≥0 => t/(r+t)) a.1 (by fun_prop) (by simp) hc.continuousOn (by simp),
    ← cfcₙ_mul (fun t : ℝ≥0 => NNReal.sqrt t * (t/(r+t))) NNReal.sqrt a.1
      ((NNReal.continuous_sqrt.mul hc).continuousOn) (by simp) (by fun_prop) (by simp)]
  apply cfcₙ_congr
  intro t _
  calc
    NNReal.sqrt t * (t/(r+t)) * NNReal.sqrt t = (NNReal.sqrt t*NNReal.sqrt t)*(t/(r+t)) := by ac_rfl
    _ = _ := by rw [NNReal.mul_self_sqrt]

lemma finiteResolvent_residual_norm (a : Positive A) (ha : τ a < ∞) (r : ℝ≥0) (hr : 0 < r) :
    ‖a.1-(Positive.conjugate (CFC.sqrt a.1) (τ.finiteResolvent a ha r hr).1).1‖ ≤ r := by
  rw [τ.finiteResolvent_conjugate]
  have hc : Continuous (fun t : ℝ≥0 => t*(t/(r+t))) := by
    fun_prop (disch := intro t; exact (add_pos_of_pos_of_nonneg hr t.2).ne')
  have hb (t : ℝ≥0) : t*(t/(r+t)) ≤ t := by
    exact mul_le_of_le_one_right' ((div_le_one (add_pos_of_pos_of_nonneg hr t.2)).mpr (le_add_of_nonneg_left r.2))
  have he : a.1-cfcₙ (fun t : ℝ≥0 => t*(t/(r+t))) a.1 =
      cfcₙ (fun t : ℝ≥0 => t-t*(t/(r+t))) a.1 := by
    change _ = cfcₙ (fun t : ℝ≥0 => id t-t*(t/(r+t))) a.1
    rw [cfcₙ_tsub id (fun t : ℝ≥0 => t*(t/(r+t))) a.1 (fun t _ => hb t) a.2
      (by fun_prop) rfl hc.continuousOn (by simp),cfcₙ_id ℝ≥0 a.1 a.2]
  rw [he]
  apply nnnorm_cfcₙ_nnreal_le
  intro t _
  rw [tsub_le_iff_right]
  have hrt : 0 < r+t := add_pos_of_pos_of_nonneg hr t.2
  apply (mul_le_mul_iff_left₀ hrt).mp
  rw [mul_add]
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hrt.ne']
  nlinarith

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma finiteResolvent_conjugate_tendsto (a : Positive A) (ha : τ a < ∞) :
    Tendsto (fun n : ℕ => Positive.conjugate (CFC.sqrt a.1)
      (τ.finiteResolvent a ha (1/(n+1)) (by positivity)).1) atTop (𝓝 a) := by
  rw [tendsto_subtype_rng,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [norm_sub_rev]
  exact τ.finiteResolvent_residual_norm a ha (1/(n+1)) (by positivity)

lemma traceNormalWeight_rep_eq_of_finite (a : Positive A) (ha : τ a < ∞) :
    τ.traceNormalWeight (τ.traceGNSPositive a) = τ a := by
  apply le_antisymm (τ.traceNormalWeight_rep_le a)
  apply (τ.lowerSemicontinuous.isClosed_preimage
    (τ.traceNormalWeight (τ.traceGNSPositive a))).mem_of_tendsto (τ.finiteResolvent_conjugate_tendsto a ha)
  refine Eventually.of_forall (fun n => ?_)
  change τ (Positive.conjugate (CFC.sqrt a.1) (τ.finiteResolvent a ha (1/(n+1)) (by positivity)).1) ≤ _
  rw [← τ.traceVectorForm_rep_positive]
  exact le_iSup (fun b : τ.FiniteTraceContraction => ENNReal.ofReal (τ.traceVectorForm b.1 b.2.1
    (τ.traceGNSRep a.1))) (τ.finiteResolvent a ha (1/(n+1)) (by positivity))

lemma traceNormalWeight_rep_eq (a : Positive A) (ha : a.1 ∈ τ.finiteIdeal) :
    τ.traceNormalWeight (τ.traceGNSPositive a) = τ a := by
  apply le_antisymm (τ.traceNormalWeight_rep_le a)
  rw [trace_eq_iSup_positive_cuts A τ a]
  apply iSup_le
  intro ε
  apply iSup_le
  intro hε
  rw [← τ.traceNormalWeight_rep_eq_of_finite (Positive.cut a ε)
    ((τ.positive_mem_finiteIdeal_iff_cuts a).mp ha ε hε)]
  apply τ.traceNormalWeight_mono
  exact OrderHomClass.mono τ.traceGNSRep (show (Positive.cut a ε).1 ≤ a.1 from Positive.cut_le a ε)

end ExtendedTrace
end TraceConeClassification

end

end OAI
