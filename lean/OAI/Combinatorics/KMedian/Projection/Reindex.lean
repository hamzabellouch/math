import Mathlib
import OAI.Combinatorics.KMedian.Projection.Repeat

namespace OAI

section Inline_PCPProjectionReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B)
variable (eu : U ≃ U') (ev : V ≃ V') (ed : D ≃ D') (es : S ≃ S')
variable (ea : A ≃ A') (eb : B ≃ B')
def reindex : BiProjection U' V' D' S' A' B' where
  edge := ((eu.prodCongr ed).symm.trans G.edge).trans (ev.prodCongr es)
  project p a := eb (G.project ((eu.prodCongr ed).symm p) (ea.symm a))

lemma reindex_perfect (h : G.Perfect) : (G.reindex eu ev ed es ea eb).Perfect := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨ea ∘ a ∘ eu.symm,eb ∘ b ∘ ev.symm,?_⟩
  intro u d
  simpa only [reindex,Function.comp_def,Equiv.symm_apply_apply,Equiv.trans_apply,
    Equiv.prodCongr_apply,Equiv.prodCongr_symm,Prod.map_apply,Prod.map] using congrArg eb (h (eu.symm u) (ed.symm d))
lemma reindex_consistent (h : G.Consistent) : (G.reindex eu ev ed es ea eb).Consistent := by
  intro u d e he a
  have hh : (G.edge (eu.symm u,ed.symm d)).1=(G.edge (eu.symm u,ed.symm e)).1 := ev.injective he
  exact congrArg eb (h (eu.symm u) (ed.symm d) (ed.symm e) hh (ea.symm a))

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B']
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Fintype V'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma reindex_score (a : U' → A') (b : V' → B') :
    (G.reindex eu ev ed es ea eb).score a b=G.score (ea.symm ∘ a ∘ eu) (eb.symm ∘ b ∘ ev) := by
  unfold score
  rw [← Fintype.expect_equiv eu (fun u => 𝔼 d : D', if
    (G.reindex eu ev ed es ea eb).project (eu u,d) (a (eu u))=
      b ((G.reindex eu ev ed es ea eb).edge (eu u,d)).1 then (1:ℝ) else 0) _ (fun _ => rfl)]
  apply expect_congr rfl
  intro u _
  rw [← Fintype.expect_equiv ed (fun d => if
    (G.reindex eu ev ed es ea eb).project (eu u,ed d) (a (eu u))=
      b ((G.reindex eu ev ed es ea eb).edge (eu u,ed d)).1 then (1:ℝ) else 0) _ (fun _ => rfl)]
  apply expect_congr rfl
  intro d _
  simp only [reindex,Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.symm_apply_apply,
    Equiv.trans_apply,Function.comp_def,← Equiv.eq_symm_apply,Prod.map]
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Fintype V'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma reindex_sound {δ : ℝ} (h : G.Sound δ) : (G.reindex eu ev ed es ea eb).Sound δ := by
  intro a b
  rw [G.reindex_score eu ev ed es ea eb a b]
  exact h _ _
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionReindex

end OAI
