import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.MarkBridge

namespace OAI

namespace MatchingFPRAS.Variation
open Finset

lemma event_instances {A : Type*} (F₁ F₂ : Fintype A) (p : A → ℝ) (D : A → Prop) :
    @event A F₁ p D=@event A F₂ p D := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma sum_instances {A : Type*} (F₁ F₂ : Fintype A) (p : A → ℝ) :
    (letI:=F₁; ∑ a,p a)=(letI:=F₂; ∑ a,p a) := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma imageLaw_output_equiv {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : B ≃ C) (f : A → B) : imageLaw (e ∘ f)=imageLaw f ∘ e.symm := by
  classical
  funext c
  unfold imageLaw push
  apply sum_congr rfl
  intro a _
  simp only [Function.comp_apply,←Equiv.eq_symm_apply]
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance finiteStageSourceLabelDecidableEq (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance finiteStageSourceBagEdgeFintype (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K t k : ℕ) :
    Fintype ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _
local instance (w : V → V → ℚ) (K t k : ℕ) :
    Nonempty ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := ⟨(fun _=>false,fun _ _=>false)⟩
lemma source_transfer_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (p : Marked w K → ℝ) :
    tv (p ∘ sourceMarkedEquiv w K) (sourceLaw (fun x y=>(w x y:ℝ)) K D)=tv p (markedLaw w K D) := by
  have he : sourceLaw (fun x y=>(w x y:ℝ)) K D=markedLaw w K D ∘ sourceMarkedEquiv w K := by
    funext a
    exact (markedLaw_equiv w hw K D hD a).symm
  rw [he]
  exact tv_equiv (sourceMarkedEquiv w K) p (markedLaw w K D)

noncomputable def finiteSourceLaw (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    SourceMarked (fun x y=>(w x y:ℝ)) K → ℝ :=
  markedSamplerLaw w hw K D m hD hN h hq M η ∘ sourceMarkedEquiv w K
lemma finiteSourceLaw_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    0≤finiteSourceLaw w hw K D m hD hN h hq M η a := imageLaw_nonneg _ _
lemma finiteSourceLaw_sum (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    ∑ a,finiteSourceLaw w hw K D m hD hN h hq M η a=1 := by
  unfold finiteSourceLaw
  simp only [Function.comp_apply]
  rw [(sourceMarkedEquiv w K).sum_comp]
  exact imageLaw_sum _
theorem finiteSourceLaw_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (finiteSourceLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD) (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
      (sourceLaw (fun x y=>(w x y:ℝ)) K D)≤2*(η:ℝ)+(m:ℝ)⁻¹ := by
  rw [finiteSourceLaw,source_transfer_tv w hw K D (by omega)]
  exact markedSampler_tv w hw K D m hD hN hm h hq M η hη

lemma sampling_denominator_gt (T S : ℕ) (hT : 0<T) (hS : 0<S) : 1<1000*T*S := by
  have ht : 1≤T := hT
  have hs : 1≤S := hS
  nlinarith
lemma sampling_budget (T S : ℕ) (_hT : 0<T) (_hS : 0<S) :
    2*((1/(1000*T*S):ℚ):ℝ)+((1000*T*S:ℕ):ℝ)⁻¹=3/(1000*T*S) := by
  push_cast
  ring

theorem finite_source_stage_budget (w : V → V → ℚ) (hw : ∀ x y,0<w x y)
    (w₁ : V → V → ℝ) (hw₁ : ∀ x y,0≤w₁ x y)
    (hle : ∀ x y,x≠y → w₁ x y ≤ (w x y:ℝ))
    (hz : 0<Switching.partition (fun x y=>(w x y:ℝ)) ∅)
    (K T S : ℕ) (hT : 0<T) (hS : 0<S) (σ : ℝ) (hσ : 0≤σ)
    (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K))
    (M : BagPM (bags w K)) :
    let p := finiteSourceLaw w hw K (sourceD (V:=V) K) (1000*T*S)
      (sourceD_one K) Fintype.card_pos h hq M (1/(1000*T*S))
    Variation.event (Variation.iid p S)
      (fun x=>¬StageGood (fun x y=>(w x y:ℝ)) w₁ K σ x)<13/(1000*T) := by
  dsimp only
  have hN : 2≤Fintype.card (SourceVertex V K) :=
    (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial V)).trans_le (sourceVertex_card_ge K)
  let p := finiteSourceLaw w hw K (sourceD (V:=V) K) (1000*T*S)
    (sourceD_one K) Fintype.card_pos h hq M (1/(1000*T*S))
  have hv := finiteSourceLaw_tv w hw K (sourceD (V:=V) K) (1000*T*S) (sourceD_one K)
    hN (sampling_denominator_gt T S hT hS) h hq M (1/(1000*T*S)) (by positivity)
  rw [sampling_budget T S hT hS] at hv
  have hh:=source_nearby_budget (fun x y=>(w x y:ℝ)) w₁
    (fun x y=>by exact_mod_cast hw x y) hw₁ hle hz K T S hT hS σ hσ hsize p
    (finiteSourceLaw_nonneg w hw K _ _ _ _ h hq M _) ?_ ?_
  · rw [event_instances _ (inferInstance : Fintype (Fin S → SourceMarked (fun x y=>(w x y:ℝ)) K))] at hh
    exact hh
  · rw [sum_instances _ (inferInstance : Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K))]
    exact finiteSourceLaw_sum w hw K _ _ _ _ h hq M _
  · rw [tv_instances _ (inferInstance : Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K))]
    exact hv
end MatchingFPRAS.RationalSource

end OAI
