import OAI.Combinatorics.MatchingEntropy.Covariance

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Matrix

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in

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

end MatchingEntropyBounds

end

end OAI
