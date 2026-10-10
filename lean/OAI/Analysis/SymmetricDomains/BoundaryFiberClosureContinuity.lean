import Mathlib
import OAI.Analysis.SymmetricDomains.ConjugateMulActionCompact

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

theorem Biholomorph.conjugate_action_holomorphic {n m : ℕ}
    {S : Set (Affine n)} {T : Set (Affine m)} (e : Biholomorph S T)
    {Γ : Type*} [Group Γ] [MulAction Γ S]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset S (fun p => (γ • p : S).val)) (γ : Γ) :
    let _ : MulAction Γ T := conjugateMulAction e.toHomeomorph.toEquiv
    HolomorphicOnSubset T (fun p => (γ • p : T).val) := by
  let _ : MulAction Γ T := conjugateMulAction e.toHomeomorph.toEquiv
  change HolomorphicOnSubset T
    (fun p => (e.toHomeomorph (γ • e.toHomeomorph.symm p)).val)
  have h₁ := (hhol γ).comp (f := e.toHomeomorph.symm) e.holomorphic_invFun
  have h₂ := e.holomorphic_toFun.comp
    (f := fun p : T => γ • e.toHomeomorph.symm p) h₁
  exact h₂

open Set Filter Topology Metric Classical

def inwardDistance {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) (s : S) : ℝ :=
  if (A s).Nonempty then min 1 (infDist 0 (A s)) else 1

lemma inwardDistance_nonneg {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) (s : S) : 0 ≤ inwardDistance A s := by
  unfold inwardDistance
  split_ifs
  · exact le_min (by norm_num) infDist_nonneg
  · norm_num

lemma inwardDistance_le_one {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) (s : S) : inwardDistance A s ≤ 1 := by
  unfold inwardDistance
  split_ifs
  · exact min_le_left _ _
  · rfl

lemma inwardDistance_le_norm {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) {s : S} {v : E} (hv : v ∈ A s) :
    inwardDistance A s ≤ ‖v‖ := by
  rw [inwardDistance,ite_eq_left ⟨v,hv⟩]
  exact (min_le_right _ _).trans (by simpa using (infDist_le_dist_of_mem (x := (0 : E)) hv))

lemma inwardDistance_eq_zero_iff {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) (s : S) :
    inwardDistance A s = 0 ↔ (0 : E) ∈ closure (A s) := by
  by_cases h : (A s).Nonempty
  · rw [inwardDistance,ite_eq_left h,mem_closure_iff_infDist_zero h]
    constructor
    · intro he
      have hle : min 1 (infDist (0 : E) (A s)) ≤ 0 := le_of_eq he
      rcases min_le_iff.mp hle with hbad | hd
      · norm_num at hbad
      · exact le_antisymm hd infDist_nonneg
    · intro he
      simp [he]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    simp [inwardDistance,h]

theorem boundary_fiber_closure_at_continuity {S E : Type*}
    [PseudoMetricSpace S] [NormedAddCommGroup E] (A : S → Set E) (s : S)
    (hc : ContinuousAt (inwardDistance A) s)
    (hb : (s,(0 : E)) ∈ closure {p : S × E | p.2 ∈ A p.1}) :
    (0 : E) ∈ closure (A s) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hb
  have hs := continuous_fst.continuousAt.tendsto.comp ht
  have hv := continuous_snd.continuousAt.tendsto.comp ht
  have hd := (hc.tendsto.comp hs).sub hv.norm
  have he : inwardDistance A s ≤ 0 := by
    have H := le_of_tendsto hd (Filter.Eventually.of_forall fun i =>
      sub_nonpos.mpr (inwardDistance_le_norm A (hp i)))
    simpa using H
  exact (inwardDistance_eq_zero_iff A s).mp
    (le_antisymm he (inwardDistance_nonneg A s))

end Release061

end

end OAI
