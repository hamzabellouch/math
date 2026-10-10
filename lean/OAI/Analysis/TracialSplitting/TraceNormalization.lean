import OAI.Analysis.TracialSplitting.CoefficientApproximation

namespace OAI

noncomputable section

universe uA

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

open scoped Pointwise

open scoped ComplexOrder

open scoped ComplexOrder

namespace Pureness

section

open scoped ComplexOrder

open Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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

end

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
lemma convex_tracialStateCarrier : Convex ℝ (tracialStateCarrier (A := A)) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨?_,?_,?_⟩
  · change r • f 1 + s • g 1 = 1
    rw [hf.1,hg.1,← add_smul,hrs,one_smul]
  · intro a ha
    change 0 ≤ r • f a + s • g a
    exact add_nonneg (smul_nonneg hr (hf.2.1 a ha)) (smul_nonneg hs (hg.2.1 a ha))
  · intro a b
    change r • f (a*b) + s • g (a*b) = r • f (b*a) + s • g (b*a)
    rw [hf.2.2,hg.2.2]

end Pureness

namespace NuclearTrace

open scoped ComplexOrder

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

def traceTupleCost (x z : I → selfAdjoint A) : WeakDual ℂ A →ₗ[ℝ] ℝ where
  toFun τ := ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
  map_add' τ ρ := by
    change (∑ i, (τ (CFC.abs ((x i : A) - z i)) + ρ (CFC.abs ((x i : A) - z i))).re) = _
    simp only [Complex.add_re,Finset.sum_add_distrib]
  map_smul' r τ := by
    change (∑ i, (r • τ (CFC.abs ((x i : A) - z i))).re) =
      r • ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
    simp only [Complex.smul_re, Finset.smul_sum]

lemma traceTupleCost_continuous (x z : I → selfAdjoint A) :
    Continuous (traceTupleCost x z) := by
  apply continuous_finsetSum
  intro i _
  exact Complex.continuous_re.comp (WeakDual.eval_continuous _)

lemma traceTupleCost_eq (x z : I → selfAdjoint A) (τ : Pureness.TracialState A) :
    traceTupleCost x z τ.toWeakDual = tracialTupleSeminorm τ (x-z) := by
  rw [tracialTupleSeminorm_apply]
  rfl

lemma traceTupleCost_continuous_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) :
    Continuous (fun z => traceTupleCost x z τ.toWeakDual) := by
  simp only [traceTupleCost_eq]
  exact (tracialTupleSeminorm_continuous τ).comp (continuous_const.sub continuous_id)

lemma traceTupleCost_convex_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) {Y : Set (I → selfAdjoint A)} (hY : Convex ℝ Y) :
    ConvexOn ℝ Y (fun z => traceTupleCost x z τ.toWeakDual) := by
  refine ⟨hY,?_⟩
  intro y hy z hz r s hr hs hrs
  simp only [traceTupleCost_eq]
  have he : x - (r • y + s • z) = r • (x-y) + s • (x-z) := by
    rw [smul_sub,smul_sub]
    calc
      x - (r • y + s • z) = (r+s) • x - (r • y + s • z) := by rw [hrs,one_smul]
      _ = r • x - r • y + (s • x - s • z) := by rw [add_smul]; abel
  rw [he]
  exact (tracialTupleSeminorm τ).convexOn.2 (Set.mem_univ _) (Set.mem_univ _) hr hs hrs

theorem nuclear_uniform_tracial_coefficient_approximation
    (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (hT : Nonempty (Pureness.TracialState A)) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α, ∀ τ : Pureness.TracialState A,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let Y := (coefficientCone α).map (evalTuple x)
  let X := Pureness.tracialStateCarrier (A := A)
  have hXne : X.Nonempty := by
    obtain ⟨τ⟩ := hT
    exact ⟨τ.toWeakDual,τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩
  have hcost (τ : WeakDual ℂ A) (hτ : τ ∈ X) :
      (Pureness.tracialStateFromWeakDual τ hτ).toWeakDual = τ := by
    exact DFunLike.ext _ _ (fun _ => rfl)
  obtain ⟨z,hz,hall⟩ := @compact_convex_uniform_cost
    (WeakDual ℂ A) (I → selfAdjoint A) inferInstance inferInstance inferInstance
    inferInstance (WeakDual.instContinuousSMul ℝ) inferInstance inferInstance inferInstance
    inferInstance inferInstance X Y hXne
    Pureness.isCompact_tracialStateCarrier Pureness.convex_tracialStateCarrier
    Y.convex (fun τ z => traceTupleCost x z τ)
    (fun z _ => traceTupleCost_continuous x z)
    (fun z _ => (traceTupleCost x z).concaveOn Pureness.convex_tracialStateCarrier)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact (traceTupleCost_continuous_right x _).continuousOn)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact traceTupleCost_convex_right x _ Y.convex)
    (ε := ε) (by
      intro τ hτ
      obtain ⟨L,hL,hclose⟩ := nuclear_tracial_coefficient_approximation hA α hα
        (Pureness.tracialStateFromWeakDual τ hτ) x hε
      refine ⟨evalTuple x L,⟨L,hL,rfl⟩,?_⟩
      exact hclose)
  obtain ⟨L,hL,rfl⟩ := hz
  refine ⟨L,hL,fun τ => ?_⟩
  exact hall τ.toWeakDual ⟨τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩

end NuclearTrace

end

end OAI
