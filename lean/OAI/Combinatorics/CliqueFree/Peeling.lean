import OAI.Combinatorics.CliqueFree.Projection
import OAI.Combinatorics.CliqueFree.FiniteCoupling

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

open FiniteCoupling
lemma triangle_subgraph_surviving_le {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    (∑ t : TriangleState G, if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
      then TriangleState.weight w t else 0) ≤ 6 * triangleMass H w := by
  classical
  let S := {t : TriangleState G // H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third}
  let f : S → TriangleState H := fun t ↦ ⟨t.val.val, t.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : TriangleState H ↦ t.val) hab
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight w (f t) := rfl
    _ ≤ ∑ t : TriangleState H, TriangleState.weight w t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

lemma triangle_deletion_bound {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    6 * triangleMass G w ≤ 6 * triangleMass H w +
      3 * ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * bad (H.Adj e.src e.dst) := by
  have ht (t : TriangleState G) : TriangleState.weight w t ≤
      (if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
        then TriangleState.weight w t else 0) +
      TriangleState.weight w t * (bad (H.Adj t.first t.second) +
        bad (H.Adj t.first t.third) + bad (H.Adj t.second t.third)) := by
    have hn : 0 ≤ TriangleState.weight w t := mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)
    by_cases h1 : H.Adj t.first t.second <;> by_cases h2 : H.Adj t.first t.third <;>
      by_cases h3 : H.Adj t.second t.third <;> simp [bad,h1,h2,h3] <;> linarith
  have hs := sum_le_sum (s := univ) (fun t _ ↦ ht t)
  simp only [sum_add_distrib, mul_add] at hs
  rw [TriangleState.sum_weight] at hs
  have h13 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_flip w (fun t ↦ bad (H.Adj t.first t.second))
  have h23 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.second t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_rotate w (fun t ↦ bad (H.Adj t.first t.second))
  rw [h13,h23,TriangleState.marginal w (fun u v ↦ bad (H.Adj u v))] at hs
  have hsurv := triangle_subgraph_surviving_le (G := G) (H := H) hw
  linarith

/-- Delete exactly one unordered edge. -/
def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = u ∧ b = v ∨ a = v ∧ b = u)
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    intro hab
    apply h.2
    rcases hab with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr ⟨h2,h1⟩
    · exact Or.inl ⟨h2,h1⟩⟩
  loopless := ⟨fun a h ↦ G.irrefl h.1⟩

omit [Fintype V] in
lemma eraseEdge_le (G : SimpleGraph V) (u v : V) : eraseEdge G u v ≤ G := fun _ _ h ↦ h.1

lemma edgeMass_eraseEdge {G : SimpleGraph V} (w : V → ℝ) {u v : V} (huv : G.Adj u v) :
    edgeMass (eraseEdge G u v) w = edgeMass G w - w u * w v := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then w a * w b else 0) =
      (if (eraseEdge G u v).Adj a b then w a * w b else 0) +
      (if a = u ∧ b = v then w u * w v else 0) +
      (if a = v ∧ b = u then w v * w u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn]
    simp only [eraseEdge, h1, h2, or_self, not_false_eq_true, and_true, ite_false, add_zero]
  have he : crossMass G w univ univ = crossMass (eraseEdge G u v) w univ univ + 2 * w u * w v := by
    unfold crossMass
    simp_rw [heq,sum_add_distrib]
    simp [ite_and]

    ring
  unfold edgeMass
  linarith

lemma sum_removed_directed {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst * bad ((eraseEdge G u v).Adj e.src e.dst)) =
      f u v + f v u := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then f a b * bad ((eraseEdge G u v).Adj a b) else 0) =
      (if a = u ∧ b = v then f u v else 0) + (if a = v ∧ b = u then f v u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn,bad]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn,bad]
    by_cases ha : G.Adj a b <;> simp [eraseEdge,h1,h2,bad,ha]
  rw [EdgeState.sum_eq (fun a b ↦ f a b * bad ((eraseEdge G u v).Adj a b))]
  simp only [neighbors,sum_filter]
  simp_rw [heq,sum_add_distrib,ite_and]
  simp

lemma triangleMass_eraseEdge {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {u v : V} (huv : G.Adj u v) :
    triangleMass G w - w u * w v * commonMass G w u v ≤ triangleMass (eraseEdge G u v) w := by
  have h := triangle_deletion_bound (G := G) (H := eraseEdge G u v) hw
  rw [sum_removed_directed huv (fun a b ↦ w a * w b * commonMass G w a b), commonMass_comm G w v u] at h
  nlinarith only [h]

lemma peeling (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u v, H.Adj u v → τ ≤ commonMass H w u v) ∧
      triangleMass G w - τ * edgeMass G w ≤ triangleMass H w := by
  classical
  let S : Finset (SimpleGraph V) := univ.filter (fun H ↦ H ≤ G)
  obtain ⟨H,hHS,hmax⟩ := S.exists_max_image (fun H ↦ triangleMass H w - τ * edgeMass H w)
    ⟨G,by simp [S]⟩
  have hHG : H ≤ G := (mem_filter.1 hHS).2
  have hw0 := fun v ↦ (hw v).le
  refine ⟨H,hHG,?_,?_⟩
  · intro u v huv
    by_contra hn
    have hc : commonMass H w u v < τ := lt_of_not_ge hn
    have hle := hmax (eraseEdge H u v) (by simp [S]; exact (eraseEdge_le H u v).trans hHG)
    rw [edgeMass_eraseEdge w huv] at hle
    have ht := triangleMass_eraseEdge hw0 huv
    have hprod : 0 < w u * w v := mul_pos (hw u) (hw v)
    nlinarith [mul_lt_mul_of_pos_left hc hprod]
  · have hle := hmax G (by simp [S])
    have he := edgeMass_nonneg H hw0
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI
