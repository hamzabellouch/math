import OAI.Combinatorics.ThinTrees.MatrixMixture

namespace OAI

section

noncomputable section
open Matrix Finset Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def thresholdCrossing (q : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) : Finset (Fin m) :=
  G.crossing univ (G.partLabel (G.thresholdEdges (G.resistance X) s) q)
lemma bad_inter_eq (R : Fin m → ℝ) (t : ℝ) (B : Finset (Fin m)) :
    (univ.filter (fun e => t < R e)) ∩ B=B.filter (fun e => t < R e) := by
  ext e
  simp only [mem_inter,mem_filter,mem_univ,true_and,and_comm]
lemma resistance_domain_continuous (hn : 0 < n) (e : Fin m) :
    Continuous (fun X : G.matrixDomain => G.resistance X.val e) :=
  continuousOn_iff_continuous_domRestrict.mp (G.resistance_continuousOn hn e)
lemma threshold_stable_neighborhood (hn : 0 < n) (X : G.matrixDomain) (s : ℝ)
    (havoid : ∀e, G.resistance X.val e ≠ s) :
    ∃ε : ℝ, 0 < ε ∧ ∀Y : G.matrixDomain, dist Y X < ε →
      G.thresholdEdges (G.resistance Y.val) s=G.thresholdEdges (G.resistance X.val) s := by
  have hneigh : ∀ᶠ Y : G.matrixDomain in 𝓝 X, ∀e,
      (G.resistance Y.val e ≤ s ↔ G.resistance X.val e ≤ s) := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases hle : G.resistance X.val e ≤ s
    · have hlt := lt_of_le_of_ne hle (havoid e)
      filter_upwards [(G.resistance_domain_continuous hn e).continuousAt.eventually_lt_const hlt] with Y hY
      exact iff_of_true hY.le hle
    · have hlt := lt_of_not_ge hle
      filter_upwards [(G.resistance_domain_continuous hn e).continuousAt.eventually_const_lt hlt] with Y hY
      exact iff_of_false (not_le.mpr hY) hle
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨ε,hε,fun Y hY => ?_⟩
  ext e
  simp only [thresholdEdges, mem_filter, mem_univ, true_and]
  exact hball hY e

theorem response_limit (hn : 2 ≤ n) (hc : G.EdgeConnected 1) (q : ℕ) {t δ : ℝ} (ht : 0 < t)
    (hresponse : ∀X ∈ G.matrixDomain, ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩ G.thresholdCrossing q X s).card:ℝ) ≤
        δ*(G.thresholdCrossing q X s).card) :
    ∃X ∈ G.matrixDomain, ∀s : ℝ, (∀e, G.resistance X e ≠ s) →
      (((G.thresholdCrossing q X s).filter (fun e => 2*t < G.resistance X e)).card:ℝ) ≤
        2*δ*(G.thresholdCrossing q X s).card := by
  classical
  have hnp : 0 < n := by omega
  have hK := G.domain_compact hn
  have hne := G.domain_nonempty hnp hc
  have hcv := G.domain_convex
  have hr (X : G.matrixDomain) : ∃Y : G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y.val e)) ∩ G.thresholdCrossing q X.val s).card:ℝ) ≤
        δ*(G.thresholdCrossing q X.val s).card := by
    obtain ⟨Y,hY,h⟩ := hresponse X.val X.property
    exact ⟨⟨Y,hY⟩,h⟩
  choose R hR using hr
  have heps (p : ℕ) : (0:ℝ) < 1/((p:ℝ)+1) := by positivity
  choose Xp C w hw hw1 heq hnear using fun p => response_fixed_point hK hne hcv R (heps p)
  let : CompactSpace G.matrixDomain := isCompact_iff_compactSpace.mp hK
  let : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  obtain ⟨X,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq (x := Xp) (fun _ => Set.mem_univ _)
  have hnearTime : Tendsto (fun p => 1/((φ p:ℝ)+1)+dist (Xp (φ p)) X) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).add
      (tendsto_iff_dist_tendsto_zero.mp hlim)
  refine ⟨X.val,X.property,fun s havoid => ?_⟩
  let B := G.thresholdCrossing q X.val s
  obtain ⟨ε,hε,hεspec⟩ := G.threshold_stable_neighborhood hnp X s havoid
  have hstable : ∀ᶠ p in atTop, ∀c ∈ C (φ p), 0 < w (φ p) c →
      G.thresholdCrossing q c.val s=B := by
    filter_upwards [hnearTime.eventually_lt_const hε] with p hp
    intro c hc hwc
    have hd : dist c X < ε := by
      have hh := hnear (φ p) c hc hwc
      have htri := dist_triangle c (Xp (φ p)) X
      linarith
    unfold thresholdCrossing
    rw [hεspec c hd]
    rfl
  have hcounts : ∀ᶠ p in atTop,
      ((B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e)).card:ℝ) ≤ 2*δ*B.card := by
    filter_upwards [hstable] with p hp
    apply mixture_bad_bound B G.incidence (C (φ p)) (w (φ p)) (fun c => (R c).val)
      (hw (φ p)) (hw1 (φ p)) (fun c _ => G.domain_pd hnp (R c).property)
      (G.domain_pd hnp (Xp (φ p)).property) (heq (φ p)) ht
    intro c hc hwc
    have hh := hR c s
    rw [hp c hc hwc,bad_inter_eq] at hh
    exact hh
  let Bad := B.filter (fun e => 2*t < G.resistance X.val e)
  have hpersist : ∀ᶠ p in atTop, ∀e ∈ Bad, 2*t < G.resistance (Xp (φ p)).val e := by
    apply (Filter.eventually_all_finset Bad).mpr
    intro e he
    have hgt := (mem_filter.mp he).2
    exact ((G.resistance_domain_continuous hnp e).tendsto X |>.comp hlim).eventually_const_lt hgt
  obtain ⟨p,hp,hpers⟩ := (hcounts.and hpersist).exists
  have hsub : Bad ⊆ B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e) := by
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,hpers e he⟩
  exact (show (Bad.card:ℝ) ≤ (B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e)).card by
    exact_mod_cast card_le_card hsub).trans hp

end StrongThinTree.MultiGraph

end
end

end OAI
