import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inclusionInDoubleDual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro F
  let T := InnerProductSpace.toDual ℝ E
  let g : StrongDual ℝ E := F.comp T.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨T.symm g, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨y, rfl⟩ := T.surjective f
  change ⟪y, T.symm g⟫_ℝ = F (T y)
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

lemma inclusionInDoubleDualWeak_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
  intro F
  obtain ⟨x, hx⟩ := inclusionInDoubleDual_surjective
    ((StrongDual.toWeakDual : StrongDual ℝ (StrongDual ℝ E) ≃ₗ[ℝ]
      WeakDual ℝ (StrongDual ℝ E)).symm F)
  refine ⟨toWeakSpace ℝ E x, ?_⟩
  apply (StrongDual.toWeakDual : StrongDual ℝ (StrongDual ℝ E) ≃ₗ[ℝ]
      WeakDual ℝ (StrongDual ℝ E)).symm.injective
  change (NormedSpace.inclusionInDoubleDual ℝ E) x = _
  exact hx

lemma isCompact_weakImage {s : Set E} (hconv : Convex ℝ s)
    (hclosed : IsClosed s) (hbounded : IsBounded s) :
    IsCompact (toWeakSpace ℝ E '' s) := by
  have hcl : closure (toWeakSpace ℝ E '' s) = toWeakSpace ℝ E '' s := by
    rw [← hconv.toWeakSpace_closure (𝕜 := ℝ), hclosed.closure_eq]
  rw [← hcl]
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hbounded
  · rw [Set.range_eq_univ.mpr inclusionInDoubleDualWeak_surjective]
    exact subset_univ _

lemma nonempty_iInter_closed_convex {K : ℕ → Set E}
    (hne : ∀ n, (K n).Nonempty) (hcl : ∀ n, IsClosed (K n))
    (hc : ∀ n, Convex ℝ (K n)) (hanti : Antitone K) (hb : IsBounded (K 0)) :
    (⋂ n, K n).Nonempty := by
  let T := toWeakSpace ℝ E
  have himgcl : ∀ n, IsClosed (T '' K n) := by
    intro n
    rw [← (hcl n).closure_eq, (hc n).toWeakSpace_closure (𝕜 := ℝ)]
    exact isClosed_closure
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => T '' K n) (fun n => image_mono (hanti (Nat.le_succ n)))
    (fun n => (hne n).image T) (isCompact_weakImage (hc 0) (hcl 0) hb) himgcl
  refine ⟨T.symm y, mem_iInter.mpr fun n => ?_⟩
  obtain ⟨x, hx, heq⟩ := mem_iInter.mp hy n
  simpa only [← heq, LinearEquiv.symm_apply_apply] using hx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma exists_snd_of_tendsto_fst_of_bounded
    {C : Set (WithLp 2 (E × F))} (hCcl : IsClosed C) (hCconv : Convex ℝ C)
    {u : ℕ → WithLp 2 (E × F)} (hu : ∀ n, u n ∈ C)
    {f : E} (hf : Tendsto (fun n => (u n).fst) atTop (𝓝 f))
    {B : ℝ} (hB : ∀ n, ‖(u n).snd‖ ≤ B) :
    ∃ g : F, WithLp.toLp 2 (f, g) ∈ C ∧ ‖g‖ ≤ B := by
  let K : ℕ → Set (WithLp 2 (E × F)) := fun n =>
    (C ∩ WithLp.fst ⁻¹' Metric.closedBall f (1 / (n + 1 : ℝ))) ∩
      WithLp.snd ⁻¹' Metric.closedBall (0 : F) B
  have hKcl : ∀ n, IsClosed (K n) := fun _ =>
    (hCcl.inter (Metric.isClosed_closedBall.preimage (WithLp.continuous_fst 2 E F))).inter
      (Metric.isClosed_closedBall.preimage (WithLp.continuous_snd 2 E F))
  have hKconv : ∀ n, Convex ℝ (K n) := fun n =>
    (hCconv.inter ((convex_closedBall f (1 / (n + 1 : ℝ))).linear_preimage (WithLp.fstₗ 2 ℝ E F))).inter
      ((convex_closedBall (0 : F) B).linear_preimage (WithLp.sndₗ 2 ℝ E F))
  have hKanti : Antitone K := by
    intro n k hnk p hp
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    have hpdist : dist p.fst f ≤ 1 / (k + 1 : ℝ) := hp.1.2
    exact hpdist.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1))
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hf) (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨u k, ⟨⟨hu k, (hk k le_rfl).le⟩, by simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hB k⟩⟩
  have hKb : IsBounded (K 0) := by
    have hbprod : IsBounded (Metric.closedBall f (1 : ℝ) ×ˢ Metric.closedBall (0 : F) B) :=
      Metric.isBounded_closedBall.prod Metric.isBounded_closedBall
    have himg := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.lipschitzWith.isBounded_image hbprod
    apply himg.subset
    intro p hp
    refine ⟨WithLp.ofLp p, ?_, rfl⟩
    refine ⟨?_, hp.2⟩
    have hpdist : dist p.fst f ≤ 1 / (0 + 1 : ℝ) := by
      simpa only [mem_preimage, Metric.mem_closedBall, Nat.cast_zero] using hp.1.2
    simpa only [zero_add, div_one, Metric.mem_closedBall, WithLp.ofLp_fst] using hpdist
  obtain ⟨p, hp⟩ := nonempty_iInter_closed_convex hKne hKcl hKconv hKanti hKb
  have hpf : p.fst = f := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hbound : ∀ n : ℕ, dist p.fst f ≤ 1 / (n + 1 : ℝ) := fun n => (mem_iInter.mp hp n).1.2
    exact ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hbound)
  refine ⟨p.snd, ?_, ?_⟩
  · have heq : WithLp.toLp 2 (f, p.snd) = p := by
      rw [← hpf]
      rfl
    rw [heq]
    exact (mem_iInter.mp hp 0).1.1
  · simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hp 0).2

end WeakHessianFunctional

end
end InlinedFile0

end OAI
