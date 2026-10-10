import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.EdgeFamilyDegree
import OAI.Combinatorics.TriangleRemoval.Process.CardBiUnion
import OAI.Combinatorics.TriangleRemoval.Probability.AbsPmfMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem averaged_singleton_survival_error {n : ℕ} (G : Graph n) (hne : G.Nonempty)
    (D ε : ℝ) (hD : 0 < D)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε) :
    |pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e})-
      cavityReference D 1| ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        collisionCost (triangleHypergraph G) {e} none)+ε*cavityReference D 1 := by
  let P := PMF.uniformOfFinset G hne
  have hh := pmfMean_common_error P (fun e => focusSurvival G {e})
    (fun e => collisionCost (triangleHypergraph G) {e} none+ε*cavityReference D 1)
    (cavityReference D 1) (fun e he => singleton_survival_error G D ε hD hrel e
      ((PMF.mem_support_uniformOfFinset_iff hne e).mp he))
  simpa only [pmfMean_add,pmfMean_const,P] using hh

theorem averaged_pair_survival_error {n : ℕ} (G : Graph n) (hne : G.Nonempty)
    (hG : G ⊆ completeGraph n) (D ε : ℝ) (hD : 0 < D) (hε : 0 ≤ ε)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε) :
    |pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f}))-
        (cavityReference D 1)^2| ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
          collisionCost (triangleHypergraph G) {e,f} none else 0))+
      rootOverlap G hne+(2*ε+ε^2)*(cavityReference D 1)^2 := by
  classical
  let P := PMF.uniformOfFinset G hne
  let A := (2*ε+ε^2)*(cavityReference D 1)^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let err := fun e f : Finset (Fin n) =>
    (if Disjoint e f then collisionCost (triangleHypergraph G) {e,f} none else 0)+
      (if ¬Disjoint e f then 1 else 0)+A
  have ht (e f : Finset (Fin n)) (he : e ∈ P.support) (hf : f ∈ P.support) :
      |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤ err e f := by
    have heG := (PMF.mem_support_uniformOfFinset_iff hne e).mp he
    have hfG := (PMF.mem_support_uniformOfFinset_iff hne f).mp hf
    by_cases hd : Disjoint e f
    · have hh := pair_survival_error G D ε hD hε hrel e f heG hfG
        (disjoint_valid_edge_ne (mem_completeGraph.mp (hG heG)) hd)
      simpa only [err,hd,not_true_eq_false,ite_true,ite_false,add_zero,A] using hh
    · have hsu := focusSurvival_mem_unit G {e,f}
      have hr := (cavityReference_pos hD (by norm_num : (0 : ℝ) ≤ 1)).le
      have hru := cavityReference_le_one hD (by norm_num : (0 : ℝ) ≤ 1)
      have hsq : (cavityReference D 1)^2 ≤ 1 := by nlinarith
      have hh : |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsu.1,hsu.2,sq_nonneg (cavityReference D 1)]
      simpa only [err,hd,not_false_eq_true,ite_true,ite_false,zero_add] using
        hh.trans (le_add_of_nonneg_right hA)
  have hh := pmfMean_common_error P
    (fun e => pmfMean P (fun f => focusSurvival G {e,f}))
    (fun e => pmfMean P (err e)) ((cavityReference D 1)^2)
    (fun e he => pmfMean_common_error P (fun f => focusSurvival G {e,f})
      (err e) ((cavityReference D 1)^2) (fun f hf => ht e f he hf))
  simpa only [err,pmfMean_add,pmfMean_const,A,P,rootOverlap] using hh

lemma currentDegree_eq_edgeFamilyDegree {n : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u : Fin n) :
    currentDegree G u = edgeFamilyDegree G u := by
  classical
  unfold currentDegree edgeFamilyDegree
  apply Finset.card_bij (fun v _ => ({u,v} : Finset (Fin n)))
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,by simp⟩
  · intro v _ w _ h
    by_cases huv : u = v
    · subst v
      have hw' : w ∈ ({u,u} : Finset (Fin n)) := by rw [h]; simp
      have hwu : w = u := by simpa using hw'
      exact hwu.symm
    · have hv' : v ∈ ({u,w} : Finset (Fin n)) := by rw [← h]; simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
      rcases hv' with h' | h'
      · exact False.elim (huv h'.symm)
      · exact h'
  · intro e he
    obtain ⟨heG,hue⟩ := Finset.mem_filter.mp he
    obtain ⟨a,b,_,heq⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (hG heG))
    subst e
    simp only [Finset.mem_insert,Finset.mem_singleton] at hue
    rcases hue with rfl | rfl
    · exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heG⟩,rfl⟩
    · refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · simpa only [Finset.pair_comm] using heG
      · exact Finset.pair_comm _ _

theorem goodPrefix_rootOverlap {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
    ∀ hne : G.Nonempty, rootOverlap G hne ≤ 8/(n : ℝ) := by
  have hδ : Tendsto (fun n : ℕ => (n : ℝ)^(-c)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hδ.eventually_le_const zero_lt_one,prefixDensity_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hδ hp hn
  intro C G hG hne
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < prefixDensity n :=
    (Real.rpow_pos_of_pos hn0 _).trans_le hp.1
  have hdeg (v : Fin n) : (edgeFamilyDegree G v : ℝ) ≤ 2*(n : ℝ)*prefixDensity n := by
    have hh := (abs_le.mp (hG.2.2.1 v)).2
    have hmul := mul_le_mul_of_nonneg_right hδ (mul_nonneg hn0.le hp0.le)
    rw [← currentDegree_eq_edgeFamilyDegree G hG.1 v]
    nlinarith
  apply (rootOverlap_le_maxDegree G hne
    (fun e he => mem_completeGraph.mp (hG.1 he)) (2*(n : ℝ)*prefixDensity n) hdeg).trans_eq
  rw [hG.2.1,prefixM]
  field_simp [ne_of_gt hn0,ne_of_gt hp0]
  ring

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
