import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.TraceExistence
import OAI.Analysis.JiangSu.DimensionDrop.Matching
import OAI.Analysis.JiangSu.MatrixAlgebras.CStarProjectionRounding

namespace OAI


noncomputable section
namespace CStarProjectionRounding
open scoped CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma norm_selfAdjointPart_le (a : A) : ‖(selfAdjointPart ℝ a : A)‖≤‖a‖ := by
  rw [selfAdjointPart_apply_coe,norm_smul]
  have h := norm_add_le a (star a)
  rw [norm_star] at h
  norm_num [invOf_eq_inv] at *
  nlinarith

lemma map_selfAdjointPart (φ : A →⋆ₐ[ℂ] B) (a : A) :
    φ (selfAdjointPart ℝ a : A)=(selfAdjointPart ℝ (φ a) : B) := by
  simp only [selfAdjointPart_apply_coe]
  change φ.toAlgHom ((⅟2 : ℝ) • (a+star a)) = _
  rw [φ.toAlgHom.map_smul_of_tower]
  simp only [StarAlgHom.coe_toAlgHom, map_add,map_star]

lemma defect_near_projection {b e : B} (he : IsStarProjection e)
    (h : ‖b-e‖<1/64) : ‖b-b*b‖≤1/16 := by
  have heN : ‖e‖≤1 := he.norm_le e
  have hbN : ‖b‖≤2 := by
    have hh := norm_add_le (b-e) e
    rw [sub_add_cancel] at hh
    linarith
  have hid : b-b*b=(b-e)-(b*(b-e)+(b-e)*e) := by
    noncomm_ring [he.isIdempotentElem.eq]
  calc
    ‖b-b*b‖=‖(b-e)-(b*(b-e)+(b-e)*e)‖ := congrArg norm hid
    _≤‖b-e‖+‖b*(b-e)+(b-e)*e‖ := norm_sub_le _ _
    _≤‖b-e‖+(‖b*(b-e)‖+‖(b-e)*e‖) := add_le_add_right (norm_add_le _ _) _
    _≤‖b-e‖+(‖b‖*‖b-e‖+‖b-e‖*‖e‖) :=
      add_le_add_right (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) _
    _≤4*‖b-e‖ := by nlinarith [norm_nonneg (b-e),mul_le_mul_of_nonneg_right hbN (norm_nonneg (b-e)),
      mul_le_mul_of_nonneg_left heN (norm_nonneg (b-e))]
    _≤1/16 := by linarith

lemma trivial_projection_of_approximation (φ : A →⋆ₐ[ℂ] B) (hφ : Isometry φ)
    (hA : ∀ q : A, IsStarProjection q → q=0 ∨ q=1)
    {e : B} (he : IsStarProjection e) {a : A} (ha : ‖e-φ a‖<1/64) : e=0 ∨ e=1 := by
  let b : A := selfAdjointPart ℝ a
  have hbsa : IsSelfAdjoint b := (selfAdjointPart ℝ a).property
  have hbnear : ‖φ b-e‖<1/64 := by
    have hid : φ b-e=(selfAdjointPart ℝ (φ a-e) : B) := by
      rw [show φ b=(selfAdjointPart ℝ (φ a) : B) from map_selfAdjointPart φ a]
      rw [map_sub]
      change (selfAdjointPart ℝ (φ a) : B)-e=
        (selfAdjointPart ℝ (φ a) : B)-(selfAdjointPart ℝ e : B)
      rw [he.isSelfAdjoint.coe_selfAdjointPart_apply ℝ]
    rw [hid]
    exact (norm_selfAdjointPart_le _).trans_lt (by simpa only [norm_sub_rev] using ha)
  have hnorm (x : A) : ‖φ x‖=‖x‖ := by
    simpa only [map_zero,dist_zero_right] using hφ.dist_eq x 0
  have hbdef : ‖b-b*b‖≤1/16 := by
    rw [←hnorm (b-b*b),map_sub,map_mul]
    exact defect_near_projection he hbnear
  obtain ⟨q,hq,hqb⟩ := exists_nearby_projection hbsa hbdef
  have hdist : ‖φ q-e‖<1 := by
    calc
      ‖φ q-e‖≤‖φ q-φ b‖+‖φ b-e‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _=‖q-b‖+‖φ b-e‖ := by rw [←map_sub,hnorm]
      _<1 := by linarith
  rcases hA q hq with hq0|hq1
  · left
    rw [hq0,map_zero,zero_sub,norm_neg] at hdist
    exact idempotent_of_norm_lt_one he.isIdempotentElem hdist
  · right
    rw [hq1,map_one] at hdist
    exact (sub_eq_zero.mp (idempotent_of_norm_lt_one he.one_sub.isIdempotentElem hdist)).symm
end CStarProjectionRounding

namespace SequentialCStar.System
open CStarProjectionRounding

variable {C : ℕ → Type*} [∀ n, CStarAlgebra (C n)] [∀ n, Nontrivial (C n)]
variable (S : SequentialCStar.System C)

theorem limit_projection_trivial (h : ∀ n (e : C n), IsStarProjection e → e=0 ∨ e=1)
    (p : S.Limit) (hp : IsStarProjection p) : p=0 ∨ p=1 := by
  obtain ⟨n,a,ha⟩ := S.finite_stage_approximation p (show (0:ℝ)<1/64 by norm_num)
  exact trivial_projection_of_approximation (S.inclusion n) (S.inclusion_isometry n) (h n) hp ha

end SequentialCStar.System


namespace OriginalJiangSu
open JiangSuConstruction

theorem projection_trivial (e : Algebra) (he : IsStarProjection e) : e=0 ∨ e=1 := by
  apply system.limit_projection_trivial _ e he
  intro n q hq
  exact primeDrop_idempotent_trivial (by have := (pair n).p_gt; omega)
    (by have := (pair n).q_gt; omega) (pair n).coprime q hq.isIdempotentElem

open scoped CStarAlgebra ComplexOrder

local instance tracePNeZero (n : ℕ) : NeZero (pair n).p :=
  ⟨by have := (pair n).p_gt; omega⟩
local instance traceQNeZero (n : ℕ) : NeZero (pair n).q :=
  ⟨by have := (pair n).q_gt; omega⟩

lemma stage_trace_oscillation (n : ℕ) (f : Stage n) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ s t : Interval,
      ‖normalizedTracePath (system.map (Nat.le_add_right n k) f).val s-
        normalizedTracePath (system.map (Nat.le_add_right n k) f).val t‖<ε := by
  classical
  obtain ⟨k,W,-,hW⟩ := stage_matching n {f} hε
  refine ⟨k,?_⟩
  intro s t
  let g := system.map (Nat.le_add_right n k) f
  have hb := normalizedMatrixTrace_norm
    (unitaryConjugation (W (s,t)) (g.val s)-g.val t)
  rw [map_sub matrixTrace,matrixTrace_unitary,mul_sub] at hb
  exact hb.trans_lt (hW f (Finset.mem_singleton_self f) s t)

lemma trace_stage_unique
    (τ σ : Algebra →L[ℂ] ℂ)
    (hτ : ∀ a b,τ (a*b)=τ (b*a)) (hσ : ∀ a b,σ (a*b)=σ (b*a))
    (hτ1 : τ 1=1) (hσ1 : σ 1=1) (hτn : ‖τ‖≤1) (hσn : ‖σ‖≤1)
    (n : ℕ) (f : Stage n) :
    τ (system.inclusion n f)=σ (system.inclusion n f) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,hk⟩ := stage_trace_oscillation n f (half_pos hε)
  let g : Stage (n+k) := system.map (Nat.le_add_right n k) f
  have hg (s : Interval) :
      ‖normalizedTracePath g.val s-normalizedTracePath g.val leftEndpoint‖≤ε/2 := by
    exact (hk s leftEndpoint).le
  let T : Stage (n+k) →ₗ[ℂ] ℂ := τ.toLinearMap.comp (system.inclusion (n+k)).toLinearMap
  let S : Stage (n+k) →ₗ[ℂ] ℂ := σ.toLinearMap.comp (system.inclusion (n+k)).toLinearMap
  have hT : ∀ a b,T (a*b)=T (b*a) := by
    intro a b
    change τ (system.inclusion (n+k) (a*b))=τ (system.inclusion (n+k) (b*a))
    rw [map_mul (system.inclusion (n+k)),map_mul (system.inclusion (n+k)),hτ]
  have hS : ∀ a b,S (a*b)=S (b*a) := by
    intro a b
    change σ (system.inclusion (n+k) (a*b))=σ (system.inclusion (n+k) (b*a))
    rw [map_mul (system.inclusion (n+k)),map_mul (system.inclusion (n+k)),hσ]
  have hT1 : T 1=1 := by change τ (system.inclusion (n+k) 1)=1; rw [map_one,hτ1]
  have hS1 : S 1=1 := by change σ (system.inclusion (n+k) 1)=1; rw [map_one,hσ1]
  have hTb (a) : ‖T a‖≤‖a‖ := by
    calc _ ≤ ‖τ‖*‖system.inclusion (n+k) a‖ := τ.le_opNorm _
         _ ≤ 1*‖system.inclusion (n+k) a‖ := mul_le_mul_of_nonneg_right hτn (norm_nonneg _)
         _ = ‖a‖ := by rw [one_mul,system.inclusion_norm]
  have hSb (a) : ‖S a‖≤‖a‖ := by
    calc _ ≤ ‖σ‖*‖system.inclusion (n+k) a‖ := σ.le_opNorm _
         _ ≤ 1*‖system.inclusion (n+k) a‖ := mul_le_mul_of_nonneg_right hσn (norm_nonneg _)
         _ = ‖a‖ := by rw [one_mul,system.inclusion_norm]
  have ht := dimensionDrop_trace_oscillation T hT hT1 hTb g leftEndpoint (half_pos hε).le hg
  have hs := dimensionDrop_trace_oscillation S hS hS1 hSb g leftEndpoint (half_pos hε).le hg
  have hinc : system.inclusion (n+k) g=system.inclusion n f :=
    system.inclusion_compatible _ _
  have ht' : T g=τ (system.inclusion n f) := congrArg τ hinc
  have hs' : S g=σ (system.inclusion n f) := congrArg σ hinc
  rw [ht'] at ht
  rw [hs'] at hs
  have hh := norm_sub_le (τ (system.inclusion n f)-normalizedTracePath g.val leftEndpoint)
    (σ (system.inclusion n f)-normalizedTracePath g.val leftEndpoint)
  simp only [sub_sub_sub_cancel_right] at hh
  linarith

theorem trace_unique
    (τ σ : Algebra →L[ℂ] ℂ)
    (hτ : ∀ a b,τ (a*b)=τ (b*a)) (hσ : ∀ a b,σ (a*b)=σ (b*a))
    (hτ1 : τ 1=1) (hσ1 : σ 1=1) (hτn : ‖τ‖≤1) (hσn : ‖σ‖≤1) : τ=σ := by
  ext x
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n,f,hf⟩ := system.finite_stage_approximation x (half_pos hε)
  have he := trace_stage_unique τ σ hτ hσ hτ1 hσ1 hτn hσn n f
  have ht : ‖τ x-τ (system.inclusion n f)‖<ε/2 := by
    rw [←map_sub]
    exact (τ.le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right hτn (norm_nonneg _)).trans_lt (by simpa using hf))
  have hs : ‖σ x-σ (system.inclusion n f)‖<ε/2 := by
    rw [←map_sub]
    exact (σ.le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right hσn (norm_nonneg _)).trans_lt (by simpa using hf))
  have hh := norm_sub_le (τ x-τ (system.inclusion n f)) (σ x-σ (system.inclusion n f))
  rw [he,sub_sub_sub_cancel_right] at hh
  rw [he] at ht
  linarith

def stageTrace (n : ℕ) : Stage n →ₗ[ℂ] ℂ :=
  ((Fintype.card (Fin (pair n).p×Fin (pair n).q):ℂ)⁻¹ • matrixTrace).comp
    (((evalHom _ _ leftEndpoint).comp (dimensionDrop _ _).subtype).toLinearMap)

lemma stageTrace_norm (n : ℕ) (a : Stage n) : ‖stageTrace n a‖≤‖a‖ :=
  (normalizedMatrixTrace_norm (a.val leftEndpoint)).trans (a.val.norm_coe_le_norm leftEndpoint)
lemma stageTrace_one (n : ℕ) : stageTrace n 1=1 := normalizedMatrixTrace_one
lemma stageTrace_tracial (n : ℕ) (a b : Stage n) :
    stageTrace n (a*b)=stageTrace n (b*a) := by
  change _*matrixTrace (a.val leftEndpoint*b.val leftEndpoint)=_*matrixTrace (b.val leftEndpoint*a.val leftEndpoint)
  rw [matrixTrace_mul_comm]

def trace : Algebra →L[ℂ] ℂ :=
  SequentialCStar.limitTrace stageTrace stageTrace_norm system
lemma trace_one : trace 1=1 :=
  SequentialCStar.limitTrace_normalized _ _ _ stageTrace_one
lemma trace_tracial (a b : Algebra) : trace (a*b)=trace (b*a) :=
  SequentialCStar.limitTrace_tracial _ _ _ stageTrace_tracial a b
lemma trace_norm : ‖trace‖≤1 := SequentialCStar.limitTrace_norm _ _ _

theorem existsUnique_trace :
    ∃! τ : Algebra →L[ℂ] ℂ,
      (∀ a b,τ (a*b)=τ (b*a)) ∧ τ 1=1 ∧ ‖τ‖≤1 := by
  refine ⟨trace,⟨trace_tracial,trace_one,trace_norm⟩,?_⟩
  intro σ hσ
  exact trace_unique σ trace hσ.1 trace_tracial hσ.2.1 trace_one hσ.2.2 trace_norm

end OriginalJiangSu

end

end OAI
