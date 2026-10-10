import OAI.Analysis.Pureness.Traces.TracialStates
import Mathlib.Analysis.Normed.Module.WeakDual

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
open Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma TracialState.norm_apply_le_four (τ : TracialState A) (a : A) :
    ‖τ.functional a‖ ≤ 4 * ‖a‖ := by
  obtain ⟨y, hypos, hynorm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
  nth_rw 1 [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc
    _ ≤ ∑ i : Fin 4, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hb := τ.functional.norm_apply_le_of_nonneg (y i) (hypos i)
      rw [τ.normalized, norm_one, one_mul] at hb
      exact hb.trans (hynorm i)
    _ = _ := by simp

noncomputable def TracialState.toWeakDual (τ : TracialState A) : WeakDual ℂ A :=
  StrongDual.toWeakDual
    { toLinearMap := τ.functional.toLinearMap, cont := map_continuous τ.functional }

@[simp] lemma TracialState.toWeakDual_apply (τ : TracialState A) (a : A) :
    τ.toWeakDual a = τ.functional a := rfl

lemma TracialState.toWeakDual_injective : Function.Injective (TracialState.toWeakDual (A := A)) := by
  intro τ ρ h
  have heq : τ.functional = ρ.functional := PositiveLinearMap.ext
    (fun a => congrArg (fun f : WeakDual ℂ A => f a) h)
  cases τ
  cases ρ
  congr

noncomputable instance : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced TracialState.toWeakDual inferInstance

lemma TracialState.isEmbedding_toWeakDual :
    Topology.IsEmbedding (TracialState.toWeakDual (A := A)) :=
  TracialState.toWeakDual_injective.isEmbedding_induced

noncomputable def tracialStateCarrier : Set (WeakDual ℂ A) :=
  {f | f 1 = 1 ∧ (∀ a, 0 ≤ a → 0 ≤ f a) ∧ ∀ a b, f (a * b) = f (b * a)}

noncomputable def tracialStateFromWeakDual (f : WeakDual ℂ A) (hf : f ∈ tracialStateCarrier) :
    TracialState A where
  functional :=
    { f.toStrongDual.toLinearMap with
      monotone' := by
        intro a b hab
        change f a ≤ f b
        apply sub_nonneg.mp
        rw [← map_sub]
        exact hf.2.1 (b - a) (sub_nonneg.mpr hab) }
  normalized := hf.1
  tracial := hf.2.2

lemma range_tracialState_toWeakDual :
    Set.range (TracialState.toWeakDual (A := A)) = tracialStateCarrier := by
  ext f
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.normalized, fun a ha => τ.functional.map_nonneg ha, τ.tracial⟩
  · intro hf
    refine ⟨tracialStateFromWeakDual f hf, ?_⟩
    exact DFunLike.ext _ _ (fun a => rfl)

omit [StarOrderedRing A] in
lemma isClosed_tracialStateCarrier : IsClosed (tracialStateCarrier (A := A)) := by
  have hnorm : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos : IsClosed {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} := by
    have heq : {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} =
        ⋂ a : A, ⋂ (_ : 0 ≤ a), {f : WeakDual ℂ A | 0 ≤ f a} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le continuous_const (WeakDual.eval_continuous a)
  have htrace : IsClosed {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} := by
    have heq : {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} =
        ⋂ a : A, ⋂ b : A, {f : WeakDual ℂ A | f (a * b) = f (b * a)} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (WeakDual.eval_continuous (a * b)) (WeakDual.eval_continuous (b * a))
  exact hnorm.inter (hpos.inter htrace)

lemma isCompact_tracialStateCarrier : IsCompact (tracialStateCarrier (A := A)) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 4).of_isClosed_subset
    isClosed_tracialStateCarrier
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 4
  rw [Metric.mem_closedBall, dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound f.toStrongDual (by norm_num)
  intro a
  exact (tracialStateFromWeakDual f hf).norm_apply_le_four a

noncomputable instance : CompactSpace (TracialState A) := by
  constructor
  apply TracialState.isEmbedding_toWeakDual.isCompact_iff.mpr
  simpa only [Set.image_univ, range_tracialState_toWeakDual] using isCompact_tracialStateCarrier (A := A)

lemma TracialState.continuous_eval (a : A) :
    Continuous (fun τ : TracialState A => τ.functional a) :=
  (WeakDual.eval_continuous a).comp TracialState.isEmbedding_toWeakDual.continuous

theorem isCompact_tracialState_univ : IsCompact (Set.univ : Set (TracialState A)) := isCompact_univ
end CuntzPureness

end OAI
