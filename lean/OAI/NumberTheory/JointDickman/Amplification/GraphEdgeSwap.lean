import OAI.NumberTheory.JointDickman.Counting.GraphLagSwap
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphPair

namespace OAI

/-! # Reversing an arithmetic edge preserves its multiplier and weight -/

namespace JointDickman
open Finset Classical

theorem divisorEdge_swap {a b c N n : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (hn : n ∈ divisorEdgeNew a b c N j) :
    ((n : ℤ)+j).toNat ∈ divisorEdgeNew b a c N (-j) ∧
      divisorEdgeInverse b a c ((n : ℤ)+j).toNat = divisorEdgeInverse a b c n := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  have he' : (b : ℤ)-a = (-j)*c := by linarith
  have hm' : divisorEdgeInverse a b c n ∈ divisorEdgeOld b a c N := by
    simpa only [divisorEdgeOld,mem_filter,mem_range,and_assoc,and_left_comm,and_comm] using hm
  have hends := natural_divisor_edge_endpoints hc (mem_filter.mp hm).2.2.2.1
    (mem_filter.mp hm).2.2.2.2 he
  rw [hback] at hends
  have hends' : ((n : ℤ)+j).toNat = a*((b*divisorEdgeInverse a b c n+1)/c) := by
    rw [hends,Int.toNat_natCast]
  rw [hends']
  exact divisorEdge_forward_mem hb ha hc he' hm'

theorem graphTripleSwap_edge {B T N n : ℕ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (hn : n ∈ graphTripleEdges N g) :
    ((n : ℤ)+graphTripleLag g).toNat ∈ graphTripleEdges N (graphTripleSwap g) ∧
      divisorEdgeInverse (∏ p ∈ g.2.2, p) (∏ p ∈ g.2.1, p) (∏ p ∈ g.1, p)
        ((n : ℤ)+graphTripleLag g).toNat =
      divisorEdgeInverse (∏ p ∈ g.2.1, p) (∏ p ∈ g.2.2, p) (∏ p ∈ g.1, p) n := by
  have hs := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hb : 0 < ∏ p ∈ g.2.2, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.2 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have h := divisorEdge_swap ha hb hc hadm.2.2.2.1 hadm.2.2.2.2 hn
  change ((n : ℤ)+graphTripleLag g).toNat ∈ divisorEdgeNew
    (∏ p ∈ g.2.2, p) (∏ p ∈ g.2.1, p) (∏ p ∈ g.1, p) N (graphTripleLag (graphTripleSwap g)) ∧ _
  rw [graphTripleSwap_lag hg]
  exact h

theorem graphTripleSwap_weight {B L T N n : ℕ} {τ C : ℝ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (hn : n ∈ graphTripleEdges N g) :
    graphTripleWeight B L τ C T (graphTripleSwap g) ((n : ℤ)+graphTripleLag g).toNat =
      graphTripleWeight B L τ C T g n := by
  have hs := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hb : 0 < ∏ p ∈ g.2.2, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.2 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have hswap := graphTripleSwap_edge hg hn
  have he' : ((∏ p ∈ g.2.2, p : ℕ) : ℤ)-(∏ p ∈ g.2.1, p) =
      (-graphTripleLag g)*(∏ p ∈ g.1, p) := by
    have he := hadm.2.2.2.1
    change ((∏ p ∈ g.2.1, p : ℕ) : ℤ)-(∏ p ∈ g.2.2, p) =
      graphTripleLag g*(∏ p ∈ g.1, p) at he
    linarith
  have hcop := divisor_lag_coprime_swap hadm.2.2.2.1 hadm.2.2.2.2
  have hw := firstFormPairWeight_graph (B := B) (L := L) τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    ha hb hc hadm.2.2.2.1 hadm.2.2.2.2 hn
  have hw' := firstFormPairWeight_graph (B := B) (L := L) τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    hb ha hc he' (by simpa only [Int.natAbs_neg,graphTripleLag] using hcop)
    (show ((n : ℤ)+graphTripleLag g).toNat ∈ divisorEdgeNew _ _ _ _ (-graphTripleLag g) from by
      have hh := hswap.1
      change _ ∈ divisorEdgeNew _ _ _ _ (graphTripleLag (graphTripleSwap g)) at hh
      rwa [graphTripleSwap_lag hg] at hh)
  unfold graphTripleWeight
  rw [graphTripleSwap_lag hg]
  change arithmeticGraphPairWeight B L τ C _ _ _ _ _ (-graphTripleLag g) _ = _
  dsimp only [graphTripleSwap]
  dsimp only [graphTripleLag] at *
  rw [← hw',← hw,hswap.2]
  unfold firstFormPairWeight
  ring

end JointDickman

end OAI
