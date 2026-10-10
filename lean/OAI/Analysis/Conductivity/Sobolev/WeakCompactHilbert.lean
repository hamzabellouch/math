import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma continuous_weakDual_to_weakHilbert
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] :
    Continuous (fun L : WeakDual ℝ V =>
      toWeakSpace ℝ V ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro T
  have h := WeakDual.eval_continuous (𝕜 := ℝ)
    ((InnerProductSpace.toDual ℝ V).symm T)
  convert h using 1
  ext L
  change T ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L)) =
    (WeakDual.toStrongDual L) ((InnerProductSpace.toDual ℝ V).symm T)
  rw [← InnerProductSpace.toDual_symm_apply,real_inner_comm,
    InnerProductSpace.toDual_symm_apply]

lemma isCompact_weak_closedBall
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (x : V) (r : ℝ) :
    IsCompact (toWeakSpace ℝ V '' Metric.closedBall x r) := by
  have hc := (WeakDual.isCompact_closedBall (InnerProductSpace.toDual ℝ V x) r).image
    (continuous_weakDual_to_weakHilbert (V := V))
  convert hc using 1
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ V z),?_,?_⟩
    · change dist ((InnerProductSpace.toDual ℝ V) z) ((InnerProductSpace.toDual ℝ V) x) ≤ r
      simpa only [LinearIsometryEquiv.dist_map] using (Metric.mem_closedBall.mp hz)
    · exact congrArg (toWeakSpace ℝ V) ((InnerProductSpace.toDual ℝ V).symm_apply_apply z)
  · rintro ⟨L,hL,rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L),?_,rfl⟩
    change dist ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L)) x ≤ r
    rw [← (InnerProductSpace.toDual ℝ V).symm_apply_apply x,
      LinearIsometryEquiv.dist_map]
    exact hL

lemma continuous_weak_pair
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Continuous (fun p : WeakSpace ℝ V × WeakSpace ℝ W =>
      toWeakSpace ℝ (V × W) ((toWeakSpace ℝ V).symm p.1,(toWeakSpace ℝ W).symm p.2)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro L
  let LV := L.comp (ContinuousLinearMap.inl ℝ V W)
  let LW := L.comp (ContinuousLinearMap.inr ℝ V W)
  have hV := (WeakBilin.eval_continuous (topDualPairing ℝ V).flip LV).comp (continuous_fst : Continuous (Prod.fst : WeakSpace ℝ V × WeakSpace ℝ W → WeakSpace ℝ V))
  have hW := (WeakBilin.eval_continuous (topDualPairing ℝ W).flip LW).comp (continuous_snd : Continuous (Prod.snd : WeakSpace ℝ V × WeakSpace ℝ W → WeakSpace ℝ W))
  convert hV.add hW using 1
  ext p
  change L ((toWeakSpace ℝ V).symm p.1,(toWeakSpace ℝ W).symm p.2) =
    L ((toWeakSpace ℝ V).symm p.1,0) + L (0,(toWeakSpace ℝ W).symm p.2)
  rw [← map_add]
  simp

lemma isCompact_weak_product_closedBalls
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (r s : ℝ) :
    IsCompact (toWeakSpace ℝ (V × W) ''
      (Metric.closedBall (0 : V) r ×ˢ Metric.closedBall (0 : W) s)) := by
  have h := ((isCompact_weak_closedBall (0 : V) r).prod
    (isCompact_weak_closedBall (0 : W) s)).image (continuous_weak_pair (V := V) (W := W))
  convert h using 1
  ext p
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact ⟨(toWeakSpace ℝ V x,toWeakSpace ℝ W y),⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,rfl⟩
  · rintro ⟨⟨x,y⟩,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,rfl⟩
    exact ⟨(a,b),⟨ha,hb⟩,rfl⟩

lemma isCompact_weak_closure_of_pair_bounds
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (S : Set (V × W)) {r s : ℝ}
    (hS : ∀ z ∈ S, ‖z.1‖ ≤ r ∧ ‖z.2‖ ≤ s) :
    IsCompact (closure (toWeakSpace ℝ (V × W) '' S)) := by
  let K := toWeakSpace ℝ (V × W) ''
    (Metric.closedBall (0 : V) r ×ˢ Metric.closedBall (0 : W) s)
  have hk : IsCompact K := isCompact_weak_product_closedBalls r s
  apply hk.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hk.isClosed
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨z,by simpa only [mem_prod,Metric.mem_closedBall,dist_zero_right] using hS z hz,rfl⟩

end ScalarConductivity

end
end

end OAI
