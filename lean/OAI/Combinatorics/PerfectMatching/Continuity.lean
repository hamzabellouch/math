import OAI.Combinatorics.PerfectMatching.SecondVariation
import OAI.Combinatorics.PerfectMatching.Face

namespace OAI

/-!
Boundary lower semicontinuity of maximum entropy and attainment of the entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
/-- Concavity of H follows from mixing genuine optimizing probability laws. -/
theorem maxMatchingEntropy_mix_ge (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ G.polytope) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t)*maxMatchingEntropy G x+t*maxMatchingEntropy G y ≤
      maxMatchingEntropy G ((1-t) • x+t • y) := by
  obtain ⟨p,hp,hpe⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨q,hq,hqe⟩ := maxMatchingEntropy_attained G hy
  rw [← hpe,← hqe]
  apply (entropy_mix_ge hp.1.1 hq.1.1 ht).trans
  apply entropy_le_maxMatchingEntropy
  refine ⟨convex_probabilitySimplex _ hp.1 hq.1 (sub_nonneg.mpr ht.2) ht.1 (by ring),?_⟩
  change G.meanLinear ((1-t) • p+t • q) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • G.mean p+t • G.mean q = _
  rw [hp.2,hq.2]

/-- Boundary lower semicontinuity, using the finite matching-polytope constraints.
A fixed small mixing coefficient suffices for each prescribed entropy tolerance. -/
theorem maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  intro x hx r hr
  have hn := maxMatchingEntropy_nonneg G hx
  have hden : 0 < maxMatchingEntropy G x+1 := by linarith
  have ha : 0 < min (1:ℝ) ((maxMatchingEntropy G x-r)/(maxMatchingEntropy G x+1)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hr) hden)
  obtain ⟨t,ht0,htt⟩ := exists_between ha
  have ht1 : t<1 := htt.trans_le (min_le_left _ _)
  have htb : t*(maxMatchingEntropy G x+1) < maxMatchingEntropy G x-r :=
    (lt_div_iff₀ hden).mp (htt.trans_le (min_le_right _ _))
  filter_upwards [G.polytope_eventually_expand heven hx ht0] with y hy
  have hh := maxMatchingEntropy_mix_ge G hx hy ⟨ht0.le,ht1.le⟩
  have he : (1-t) • x+t • (x+t⁻¹ • (y-x))=y := by
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp
    ring
  rw [he] at hh
  have hz := mul_nonneg ht0.le (maxMatchingEntropy_nonneg G hy)
  nlinarith

/-- The actual entropy defect attains a maximum on the closed matching polytope. -/
theorem entropyDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) (m : ℝ) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x := by
  have hc : Continuous (fun y : E → ℝ => entropyBarrier m (entropy y)) := by
    have hb : Continuous (entropyBarrier m) := by unfold entropyBarrier; fun_prop
    exact hb.comp continuous_entropy
  have hs : UpperSemicontinuousOn (entropyDefect G m) G.polytope := by
    change UpperSemicontinuousOn (fun y => entropyBarrier m (entropy y)-maxMatchingEntropy G y) G.polytope
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      hc.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

end MatchingEntropy

end

end OAI
