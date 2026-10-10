import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.PathActivity

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

lemma consumed_destination_injective {m : ℕ} (hm : Even m) (u v : E → V)
    (huv : ∀ e, u e ≠ v e) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity)
    (q : Vertex V E m × Vertex V E m) (hq : q ∈ consumedPairs u v m d)
    (q' : Vertex V E m × Vertex V E m) (hq' : q' ∈ consumedPairs u v m d)
    (hqq : q.2=q'.2) : q=q' := by
  obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
  · obtain ⟨hj,rfl⟩ := h
    obtain ⟨e',j',h' | h'⟩ := (mem_consumedPairs u v d q').mp hq'
    · obtain ⟨hj',rfl⟩ := h'
      have hx : u e=u e' := Sum.inl_injective hqq
      have hee := uses_unique hb (left_consumes hb d he hp e hj)
        (hx.symm ▸ left_consumes hb d he hp e' hj')
      subst e'
      have hjj := Option.mem_unique hj hj'
      subst j'
      rfl
    · obtain ⟨hj',rfl⟩ := h'
      have hx : u e=v e' := Sum.inl_injective hqq
      have hee := uses_unique hb (left_consumes hb d he hp e hj)
        (hx.symm ▸ right_consumes hm hb d he hp e' hj')
      subst e'
      exact (huv e hx).elim
  · obtain ⟨hj,rfl⟩ := h
    obtain ⟨e',j',h' | h'⟩ := (mem_consumedPairs u v d q').mp hq'
    · obtain ⟨hj',rfl⟩ := h'
      have hx : v e=u e' := Sum.inl_injective hqq
      have hee := uses_unique hb (right_consumes hm hb d he hp e hj)
        (hx.symm ▸ left_consumes hb d he hp e' hj')
      subst e'
      exact (huv e hx.symm).elim
    · obtain ⟨hj',rfl⟩ := h'
      have hx : v e=v e' := Sum.inl_injective hqq
      have hee := uses_unique hb (right_consumes hm hb d he hp e hj)
        (hx.symm ▸ right_consumes hm hb d he hp e' hj')
      subst e'
      have hjj := Option.mem_unique hj hj'
      subst j'
      rfl

lemma destination_nodup {m : ℕ} (hm : Even m) (u v : E → V)
    (huv : ∀ e, u e ≠ v e) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) :
    ((consumedPairs u v m d).map Prod.snd).Nodup := by
  have hn := (List.nodup_append.mp (source_lists_nodup u v U d he)).2.1
  have hnd : (consumedPairs u v m d).Nodup := List.Nodup.of_map Prod.fst hn
  exact List.Nodup.map_on (consumed_destination_injective hm u v huv R₀ U b hb d he hp) hnd

lemma consumed_fresh {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity)
    (q : Vertex V E m × Vertex V E m) (hq : q ∈ consumedPairs u v m d) :
    q.2 ∉ enlargedHoles m R₀ U := by
  obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
  · obtain ⟨hj,rfl⟩ := h
    simpa using uses_not_hole hb (left_consumes hb d he hp e hj)
  · obtain ⟨hj,rfl⟩ := h
    simpa using uses_not_hole hb (right_consumes hm hb d he hp e hj)

@[simp] lemma mem_neutral_vertex_left (m : ℕ) (d : E → HoleBlocks m) (x : V) :
    Sum.inl x ∉ pairVertices (neutralPairs m d) := by
  rw [pairVertices_neutral]
  simp

@[simp] lemma mem_neutral_vertex_right (m : ℕ) (d : E → HoleBlocks m) (e : E) (j : Fin m) :
    Sum.inr (e,j) ∈ pairVertices (neutralPairs (V := V) m d) ↔
      j ∈ (d e).neutral.flatMap (fun q => [q.1,q.2]) := by
  rw [pairVertices_neutral]
  simp only [List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,
    Sum.inr.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨e',j',hj,hee,hjj⟩
    subst e'; subst j'; exact hj
  · intro hj; exact ⟨e,j,hj,rfl,rfl⟩

@[simp] lemma mem_consumed_source_left (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) (x : V) :
    Sum.inl x ∉ (consumedPairs u v m d).map Prod.fst := by
  rw [consumed_sources]
  simp

@[simp] lemma mem_consumed_source_right (u v : E → V) (m : ℕ) (d : E → HoleBlocks m)
    (e : E) (j : Fin m) : Sum.inr (e,j) ∈ (consumedPairs u v m d).map Prod.fst ↔
      j ∈ (d e).left ∨ j ∈ (d e).right := by
  rw [consumed_sources]
  simp only [List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,
    Sum.inr.injEq,Prod.mk.injEq,List.mem_append,Option.mem_toList]
  constructor
  · rintro ⟨e',j',hj,hee,hjj⟩
    subst e'; subst j'; exact hj
  · intro hj; exact ⟨e,j,hj,rfl,rfl⟩

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_consumed_destination_right [Fintype V] [LinearOrder V] [LinearOrder E]
    (u v : E → V) (m : ℕ) (d : E → HoleBlocks m)
    (e : E) (j : Fin m) : Sum.inr (e,j) ∉ (consumedPairs u v m d).map Prod.snd := by
  simp [consumedPairs,List.map_flatMap,List.map_append,List.map_map,Function.comp_def]




lemma mem_consumed_destination_left {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) (x : V) :
    Sum.inl x ∈ (consumedPairs u v m d).map Prod.snd ↔
      ∃ e ∈ broken U, Uses u v b e x := by
  constructor
  · rintro h
    obtain ⟨q,hq,hqx⟩ := List.mem_map.mp h
    obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
    · obtain ⟨hj,rfl⟩ := h
      have hx : u e=x := Sum.inl_injective hqx
      refine ⟨e,(mem_broken U e).mpr ⟨j,(d e).left_mem (he e) hj⟩,?_⟩
      exact hx ▸ left_consumes hb d he hp e hj
    · obtain ⟨hj,rfl⟩ := h
      have hx : v e=x := Sum.inl_injective hqx
      refine ⟨e,(mem_broken U e).mpr ⟨j,(d e).right_mem (he e) hj⟩,?_⟩
      exact hx ▸ right_consumes hm hb d he hp e hj
  · rintro ⟨e,hbr,hus⟩
    have hU : (U e).Nonempty := (mem_broken U e).mp hbr
    rcases hus with ⟨hleft,hx⟩ | ⟨hright,hx⟩
    · have hsome := ((d e).left_uses (hb.1 e) hU (he e) (hp e)).mp hleft
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp hsome
      apply List.mem_map.mpr
      refine ⟨(Sum.inr (e,j),Sum.inl (u e)),?_,by simp only [hx]⟩
      apply (mem_consumedPairs u v d _).mpr
      exact ⟨e,j,Or.inl ⟨hj,rfl⟩⟩
    · have hsome := ((d e).right_uses hm (hb.1 e) hU (he e) (hp e)).mp hright
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp hsome
      apply List.mem_map.mpr
      refine ⟨(Sum.inr (e,j),Sum.inl (v e)),?_,by simp only [hx]⟩
      apply (mem_consumedPairs u v d _).mpr
      exact ⟨e,j,Or.inr ⟨hj,rfl⟩⟩

lemma internal_covered {m : ℕ} (u v : E → V) (U : E → Finset (Fin m))
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (e : E) (j : Fin m) :
    j ∈ U e ↔ Sum.inr (e,j) ∈ pairVertices (neutralPairs (V := V) m d) ∨
      Sum.inr (e,j) ∈ (consumedPairs u v m d).map Prod.fst := by
  rw [mem_neutral_vertex_right,mem_consumed_source_right,← Finset.mem_sort (· ≤ ·),← he e]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  tauto

theorem charged_set_eq {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) :
    ((enlargedHoles m R₀ U \ (pairVertices (neutralPairs m d)).toFinset) \
      ((consumedPairs u v m d).map Prod.fst).toFinset) ∪
      ((consumedPairs u v m d).map Prod.snd).toFinset =
      (residualHoles u v R₀ U b).map ⟨Sum.inl,Sum.inl_injective⟩ := by
  classical
  ext a
  cases a with
  | inl x =>
    simp only [Finset.mem_union,Finset.mem_sdiff,List.mem_toFinset,mem_enlargedHoles_left,
      mem_neutral_vertex_left,mem_consumed_source_left,not_false_eq_true,and_true,
      Finset.mem_map,Function.Embedding.coeFn_mk,Sum.inl.injEq,exists_eq_right,
      mem_residualHoles,mem_consumed_destination_left hm u v R₀ U b hb d he hp]
  | inr a =>
    obtain ⟨e,j⟩ := a
    simp only [Finset.mem_union,Finset.mem_sdiff,List.mem_toFinset,mem_enlargedHoles_right,
      mem_consumed_destination_right,or_false,Finset.mem_map,Function.Embedding.coeFn_mk,
      Sum.inl_ne_inr,and_false,exists_false]
    have hc := (internal_covered u v U d he e j).mp
    tauto

noncomputable def holeStrength (p : ℕ) (B Hu Hv : E → ℝ) : Vertex V E (4*p) → ℝ
  | Sum.inl _ => 1
  | Sum.inr (e,j) => internalStrength p (B e) (Hu e) (Hv e) j

noncomputable def neutralCharge (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) × Vertex V E (4*p) → ℝ
  | (Sum.inr (e,j),Sum.inr (_,k)) => neutralFactor p (B e) (Hu e) (Hv e) (lam e) j k
  | _ => 0

noncomputable def consumedCharge (u : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) × Vertex V E (4*p) → ℝ
  | (Sum.inr (e,j),Sum.inl x) => if x=u e then leftFactor p (B e) (Hu e) (Hv e) (lam e) j
      else rightFactor p (B e) (Hu e) (Hv e) (lam e) j
  | _ => 0

noncomputable def totalDeletionCharge (u v : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ)
    (d : E → HoleBlocks (4*p)) : ℝ :=
  ((neutralPairs (V := V) (4*p) d).map (neutralCharge p B Hu Hv lam)).prod *
    ((consumedPairs u v (4*p) d).map (consumedCharge u p B Hu Hv lam)).prod

theorem deletion_charge_trace (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam0 : ∀ e, 0 ≤ lam e)
    (hlam : ∀ e, lam e ≤ B e) (R₀ : Finset V) (U : E → Finset (Fin (4*p)))
    (b : E → Selection (4*p)) (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    ChargeTrace (realBottleneck u v p B Hu Hv lam) (enlargedHoles (4*p) R₀ U)
      ((residualHoles u v R₀ U b).map ⟨Sum.inl,Sum.inl_injective⟩)
      (totalDeletionCharge u v p B Hu Hv lam d) := by
  classical
  have hm : Even (4*p) := ⟨2*p,by omega⟩
  have hB0 : ∀ e, 0 < B e := fun e => lt_of_lt_of_le zero_lt_one (hB e)
  have hs := source_lists_nodup u v U d he
  let N := neutralPairs (V := V) (4*p) d
  let C := consumedPairs u v (4*p) d
  let H := enlargedHoles (4*p) R₀ U
  let BB := realBottleneck u v p B Hu Hv lam
  let T := holeStrength (V := V) p B Hu Hv
  let fN := neutralCharge (V := V) p B Hu Hv lam
  let fC := consumedCharge u p B Hu Hv lam
  have hsubN : ∀ a ∈ pairVertices N, a ∈ H := by
    intro a ha
    cases a with
    | inl x => exact (mem_neutral_vertex_left (4*p) d x ha).elim
    | inr a =>
      obtain ⟨e,j⟩ := a
      exact (mem_enlargedHoles_right (4*p) R₀ U e j).mpr
        ((internal_covered u v U d he e j).mpr (Or.inl ha))
  have hlocalN : ∀ q ∈ N, 0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ fN q ∧
      (∀ a, a ≠ q.1 → BB q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → BB q.2 a ≤ T q.2) ∧ fN q*T q.1*T q.2 ≤ BB q.1 q.2 := by
    intro q hq
    obtain ⟨e,r,hr,rfl⟩ := (mem_neutralPairs d q).mp hq
    refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
      (hB0 e).trans_le (le_internalStrength _ _ _ _ _),
      neutralFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _ _,?_,?_,?_⟩
    · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e r.1 a
    · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e r.2 a
    · exact neutral_local_charge u v huv p hp B Hu Hv lam hB0 hHu hHv hlam e r.1 r.2
        ((d e).neutral_lt (he e) r hr)
  have hsubC : ∀ q ∈ C, q.1 ∈ H \ (pairVertices N).toFinset := by
    intro q hq
    have hq' : q.1 ∈ C.map Prod.fst := List.mem_map.mpr ⟨q,hq,rfl⟩
    refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
    · cases hqa : q.1 with
      | inl x => exact (mem_consumed_source_left u v (4*p) d x (hqa ▸ hq')).elim
      | inr a =>
        obtain ⟨e,j⟩ := a
        rw [mem_enlargedHoles_right]
        exact (internal_covered u v U d he e j).mpr (Or.inr (hqa ▸ hq'))
    · intro hn
      exact (List.nodup_append.mp hs).2.2 q.1 (List.mem_toFinset.mp hn) q.1 hq' rfl
  have hfresh : ∀ q ∈ C, q.2 ∉ H \ (pairVertices N).toFinset := by
    intro q hq hmem
    exact consumed_fresh hm u v R₀ U b hb d he hpar q hq (Finset.mem_sdiff.mp hmem).1
  have hlocalC : ∀ q ∈ C, 0 < T q.1 ∧ 0 ≤ fC q ∧
      (∀ a, a ≠ q.1 → BB q.1 a ≤ T q.1) ∧ fC q*T q.1 ≤ BB q.1 q.2 := by
    intro q hq
    obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
    · obtain ⟨hj,rfl⟩ := h
      have hc : fC (Sum.inr (e,j),Sum.inl (u e))=leftFactor p (B e) (Hu e) (Hv e) (lam e) j := by
        simp [fC,consumedCharge]
      rw [hc]
      refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
        leftFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _,?_,?_⟩
      · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j a
      · exact left_local_charge u v huv p hp B Hu Hv lam hB0 hHu hlam e j
    · obtain ⟨hj,rfl⟩ := h
      have hc : fC (Sum.inr (e,j),Sum.inl (v e))=rightFactor p (B e) (Hu e) (Hv e) (lam e) j := by
        simp [fC,consumedCharge,(huv e).symm]
      rw [hc]
      refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
        rightFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _,?_,?_⟩
      · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j a
      · exact right_local_charge u v huv p hp B Hu Hv lam hB0 hHv hlam e j
  have htN := charge_remove_list BB T fN N H (List.nodup_append.mp hs).1 hsubN hlocalN
  have htC := charge_replace_list BB T fC C (H \ (pairVertices N).toFinset)
    (List.nodup_append.mp hs).2.1 (destination_nodup hm u v huv R₀ U b hb d he hpar) hsubC hfresh hlocalC
  have hC0 : 0 ≤ (C.map fC).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact (hlocalC q hq).2.1
  have htrace := htN.trans htC hC0
  change ChargeTrace _ _ _ (totalDeletionCharge u v p B Hu Hv lam d) at htrace
  simpa only [N,C,H,charged_set_eq hm u v R₀ U b hb d he hpar] using htrace

theorem deletion_capacity_bound (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (b : LogicalEdge V → Selection (4*p)) (hb : FamilyHoles source target (4*p) R₀ U b)
    (d : LogicalEdge V → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    ∃ hR : Even (residualHoles source target R₀ U b).card,
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH *
      totalDeletionCharge source target p (fun e => bottleneck w (source e) (target e))
        Hu Hv (logicalActivity w) d ≤
      pairingCapacity (bottleneck w) (residualHoles source target R₀ U b) hR := by
  classical
  have ht := deletion_charge_trace source target source_ne_target p hp
    (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)
    (fun e => one_le_bottleneck w _ _) hHu hHv
    (fun e => by unfold logicalActivity edgeActivity; split_ifs <;> exact (hw _ _).le)
    (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) R₀ U b hb d he hpar
  obtain ⟨hR,hle⟩ := ChargeTrace.capacity_bound_decidable _
    (fun a b => bottleneck_comm _ a b)
    (fun a b => zero_le_one.trans (one_le_bottleneck _ a b))
    (fun a b c hab hac hbc => bottleneck_ultrametric _ a b c hab hac hbc) ht hH
  have hR' : Even (residualHoles source target R₀ U b).card := by simpa using hR
  refine ⟨hR',?_⟩
  have hx := pairingCapacity_sum_inl (terminal_lt_iff (4*p)) (bottleneck w) _
    (terminal_bottleneck w p hp Hu Hv) _ hR' hR
  apply hle.trans_eq
  convert hx using 1
  rfl

noncomputable def blockCharge (p : ℕ) (B Hu Hv lam : ℝ) (d : HoleBlocks (4*p)) : ℝ :=
  (d.left.toList.map (leftFactor p B Hu Hv lam)).prod *
    (d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)).prod *
    (d.right.toList.map (rightFactor p B Hu Hv lam)).prod

lemma blockCharge_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (U : Finset (Fin (4*p))) (d : HoleBlocks (4*p))
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    blockCharge p B Hu Hv lam d =
      (if d.right.isSome then lam else 1) *
      ((d.flatten.map (fun j => vertexPotential p B Hu Hv lam (j.val+1))).prod)⁻¹ := by
  let z := fun j : Fin (4*p) => vertexPotential p B Hu Hv lam (j.val+1)
  have hleft : (d.left.toList.map (leftFactor p B Hu Hv lam)).prod =
      ((d.left.toList.map z).prod)⁻¹ := by
    cases hl : d.left with
    | none => simp
    | some j =>
      have hj := hp.1 j (by simp [hl])
      simpa [hl,z] using leftFactor_eq_potential p B Hu Hv lam j hj
  have hright : (d.right.toList.map (rightFactor p B Hu Hv lam)).prod =
      (if d.right.isSome then lam else 1) * ((d.right.toList.map z).prod)⁻¹ := by
    cases hr : d.right with
    | none => simp
    | some j =>
      have hj := hp.2.2 j (by simp [hr])
      simpa [hr,z,div_eq_mul_inv] using rightFactor_eq_potential p B Hu Hv lam hlam j hj
  have hneutral : (d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)).prod =
      (((d.neutral.flatMap (fun q => [q.1,q.2])).map z).prod)⁻¹ := by
    have hh : d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)=
        d.neutral.map (fun q => (z q.1*z q.2)⁻¹) := by
      apply List.map_congr_left
      intro q hq
      exact neutralFactor_eq_potential p B Hu Hv lam hlam q.1 q.2
        (d.neutral_lt he q hq) (hp.2.1 q hq).1 (hp.2.1 q hq).2
    rw [hh]
    simp only [List.flatMap_def]
    simp [List.prod_inv,Function.comp_def]
  unfold blockCharge
  rw [hleft,hright,hneutral]
  simp only [HoleBlocks.flatten,List.map_append,List.prod_append,mul_inv_rev]
  change _ = (if d.right.isSome then lam else 1) * _
  ring

noncomputable def pathConstant (p : ℕ) (B Hu Hv : ℝ) : ℝ :=
  (∏ r : Fin p, max B (Hu/2^r.val)) * (∏ r : Fin p, max B (Hv/2^r.val))

lemma forcing_weight_charge (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 < lam)
    (U : Finset (Fin (4*p))) (b : Selection (4*p)) (hb : Valid U b)
    (d : HoleBlocks (4*p)) (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    (if U.Nonempty then selectedWeight (profileActivity p B Hu Hv lam) b else pathConstant p B Hu Hv) =
      pathConstant p B Hu Hv * blockCharge p B Hu Hv lam d := by
  classical
  rw [blockCharge_potential p B Hu Hv lam hlam.ne' U d he hp]
  by_cases hU : U.Nonempty
  · rw [ite_eq_left hU]
    let z : Fin (4*p+2) → ℝ := fun i => vertexPotential p B Hu Hv lam i.val
    have hprof : (fun i : Fin (4*p+1) => z i.castSucc*z i.succ)=profileActivity p B Hu Hv lam := by
      funext i
      exact (profile_vertexPotential p B Hu Hv lam hlam.ne' i).symm
    have hh := selectedWeight_hole_product (show Even (4*p) from ⟨2*p,by omega⟩) U b hb z
    rw [hprof,exact_profile_weight] at hh
    have hprod : (d.flatten.map (fun j => vertexPotential p B Hu Hv lam (j.val+1))).prod =
        ∏ j ∈ U, z j.succ.castSucc := by
      rw [he,((Finset.sort_perm_toList U (· ≤ ·)).map _).prod_eq,Finset.prod_map_toList]
      rfl
    have hz0 : z 0=1 := vertexPotential_zero p B Hu Hv lam
    have hzlast : z (Fin.last (4*p+1))=lam := vertexPotential_last p B Hu Hv lam
    have hr : (b (Fin.last (4*p))=true) ↔ d.right.isSome :=
      d.right_uses ⟨2*p,by omega⟩ hb hU he hp
    have hl : (if b 0 then z 0 else 1)=1 := by rw [hz0]; split_ifs <;> rfl
    simp only [Bool.false_eq_true,ite_false,mul_one,hl,hzlast] at hh
    simp only [hr] at hh
    have hz : (∏ j ∈ U, z j.succ.castSucc) ≠ 0 := by
      apply ne_of_gt
      apply Finset.prod_pos
      intro j hj
      exact vertexPotential_pos p B Hu Hv lam hB hlam _
    rw [hprod]
    change _=pathConstant p B Hu Hv * ((if d.right.isSome then lam else 1)*_)
    apply (mul_right_cancel₀ hz)
    rw [mul_assoc,mul_assoc,inv_mul_cancel₀ hz,mul_one]
    exact hh
  · rw [ite_eq_right hU]
    have hh : d.flatten=[] := by rw [he,Finset.not_nonempty_iff_eq_empty.mp hU]; simp
    have hr : d.right=none := by
      have he' := hh
      simp only [HoleBlocks.flatten,List.append_eq_nil_iff] at he'
      cases hr : d.right <;> simp_all
    simp [hh,hr]

end MatchingFPRAS.Enlargement

end OAI
