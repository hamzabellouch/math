import OAI.Probability.FreeIsing.Trees.CutContinuations
import OAI.Probability.FreeIsing.Trees.OrbitAverage
import OAI.Probability.FreeIsing.Trees.PathRerooting

namespace OAI

noncomputable section
namespace Problem367.TreeOrbitAverage
open ConnectedHull

def stemForbidden {d : ℕ} (stem : List (Fin d)) : Finset (Fin d) :=
  stem.getLast?.toFinset

theorem card_stemForbidden_le_one {d : ℕ} (stem : List (Fin d)) :
    (stemForbidden stem).card ≤ 1 := by
  unfold stemForbidden
  cases stem.getLast? <;> simp

def suffixVertex {d n : ℕ} {stem : List (Fin d)} (s : Extension stem n) : TreeVertex d :=
  ⟨s.1, s.2.2.right_of_append⟩

@[simp] theorem suffixVertex_length {d n : ℕ} {stem : List (Fin d)}
    (s : Extension stem n) : (suffixVertex s).1.length = n := s.2.1

def extensionEquivCutDescendants {d : ℕ} (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) :
    Extension stem (k + 1 + L) ≃
      {v // v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L} where
  toFun s := ⟨⟨suffixVertex s, s.2.1⟩, by
    rw [mem_descendants_avoidingTreeCut]
    intro c hc hbad
    have hc' : c ∈ stem.getLast? := by simpa only [stemForbidden, Option.mem_toFinset] using hbad
    exact (List.isChain_append.mp s.2.2).2.2 c hc' c hc rfl⟩
  invFun v := ⟨v.1.1.1, v.1.2, by
    apply hstem.append v.1.1.2
    intro c hc a ha heq
    subst a
    exact (mem_descendants_avoidingTreeCut (stemForbidden stem) v.1).mp v.2 c ha
      (by simpa only [stemForbidden, Option.mem_toFinset] using hc)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_extension_suffix {d : ℕ} (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) (f : TreeVertex d → ℝ) :
    (∑ s : Extension stem (k + 1 + L), f (suffixVertex s)) /
        (Fintype.card (Extension stem (k + 1 + L)) : ℝ) =
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L, f v.1) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  classical
  let e := extensionEquivCutDescendants stem hstem k L
  have hsum := e.sum_comp (fun v => f v.1.1)
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_coe] at hcard
  have hs : (∑ s : Extension stem (k + 1 + L), f (suffixVertex s)) =
      ∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L, f v.1 := by
    calc
      _ = ∑ v : {v // v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L},
          f v.1.1 := hsum
      _ = _ := Finset.sum_coe_sort
        (cutDescendants (avoidingTreeCut (stemForbidden stem) k) L)
        (fun v : TreeShell d (k + 1 + L) => f v.1)
  rw [hcard, hs]

theorem stripPrefixAut_extension_prefix {d n : ℕ} {stem : List (Fin d)}
    (s : Extension stem n) (i : ℕ) :
    (stripPrefixAut stem).toEquiv (takeVertex (endpoint s) (stem.length + i)) =
      takeVertex (suffixVertex s) i := by
  have hlen : stem.length ≤ (endpoint s).1.length := by
    change stem.length ≤ (stem ++ s.1).length
    simp
  have htake : (endpoint s).1.take stem.length = stem := by
    change (stem ++ s.1).take stem.length = stem
    simp
  have hdrop : dropVertex (endpoint s) stem.length = suffixVertex s := by
    apply Subtype.ext
    change (stem ++ s.1).drop stem.length = s.1
    simp
  simpa only [htake, hdrop, Nat.add_sub_cancel_left] using
    stripPrefixAut_takeVertex (endpoint s) hlen (Nat.le_add_right stem.length i)

def rootEdgeProduct {d : ℕ} (a : TreeVertex d → TreeVertex d → ℝ)
    (v : TreeVertex d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, a (takeVertex v i) (takeVertex v (i + 1))

theorem rootEdgeProduct_endpoint_le_rerooted {d n : ℕ} {stem : List (Fin d)}
    (a : TreeVertex d → TreeVertex d → ℝ)
    (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1) (s : Extension stem n) :
    rootEdgeProduct a (endpoint s) ≤
      rootEdgeProduct (fun u v => a ((stripPrefixAut stem).toEquiv.symm u)
        ((stripPrefixAut stem).toEquiv.symm v)) (suffixVertex s) := by
  unfold rootEdgeProduct
  have hlen : (endpoint s).1.length = stem.length + n := by
    simp only [endpoint, List.length_append, s.2.1]
  rw [hlen, Finset.prod_range_add]
  have hpre : (∏ i ∈ Finset.range stem.length,
      a (takeVertex (endpoint s) i) (takeVertex (endpoint s) (i + 1))) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => (ha _ _).1) (fun _ _ => (ha _ _).2)
  have hnonneg : 0 ≤ (∏ j ∈ Finset.range n,
      a (takeVertex (endpoint s) (stem.length + j))
        (takeVertex (endpoint s) (stem.length + j + 1))) :=
    Finset.prod_nonneg (fun _ _ => (ha _ _).1)
  refine (mul_le_mul_of_nonneg_right hpre hnonneg).trans_eq ?_
  rw [one_mul, suffixVertex_length]
  apply Finset.prod_congr rfl
  intro i hi
  have h (j : ℕ) : (stripPrefixAut stem).toEquiv.symm (takeVertex (suffixVertex s) j) =
      takeVertex (endpoint s) (stem.length + j) := by
    rw [← stripPrefixAut_extension_prefix s j, Equiv.symm_apply_apply]
  dsimp only
  rw [h i, h (i + 1), Nat.add_assoc]

theorem average_rootEdgeProduct_endpoint_le_rerooted {d : ℕ}
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    (a : TreeVertex d → TreeVertex d → ℝ)
    (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1) :
    (∑ s : Extension stem (k + 1 + L), rootEdgeProduct a (endpoint s)) /
        (Fintype.card (Extension stem (k + 1 + L)) : ℝ) ≤
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
        rootEdgeProduct (fun u w => a ((stripPrefixAut stem).toEquiv.symm u)
          ((stripPrefixAut stem).toEquiv.symm w)) v.1) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  rw [← average_extension_suffix stem hstem k L]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun s _ => rootEdgeProduct_endpoint_le_rerooted a ha s)

end Problem367.TreeOrbitAverage

end

end OAI
