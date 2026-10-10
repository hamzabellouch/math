import OAI.Combinatorics.CliqueFree.Projection

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
variable {G : SimpleGraph V}

noncomputable def graph (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) : SimpleGraph (EdgeState G) where
  Adj a b := ∃ e, good e ∧ good e.rev ∧ F e = a ∧ F e.rev = b
  symm := ⟨by
    rintro a b ⟨e, he, hr, ha, hb⟩
    exact ⟨e.rev, hr, by simpa using he, hb, by simpa using ha⟩⟩
  loopless := ⟨by
    rintro a ⟨e, he, hr, ha, hb⟩
    have heq : e.src = e.dst := by
      calc
        e.src = (F e).src := (hF e).symm
        _ = (F e.rev).src := congrArg EdgeState.src (ha.trans hb.symm)
        _ = e.dst := hF e.rev
    exact e.adj.ne heq⟩

omit [Fintype V] in
lemma projection (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) :
    EdgeProjection (graph F hF good) G EdgeState.src := by
  have endpoints {a b : EdgeState G} {e : EdgeState G} (ha : F e = a) (hb : F e.rev = b) :
      a.src = e.src ∧ b.src = e.dst :=
    ⟨by rw [← ha, hF], by rw [← hb, hF]; rfl⟩
  constructor
  · rintro a b ⟨e, _, _, ha, hb⟩
    obtain ⟨hs, ht⟩ := endpoints ha hb
    rw [hs, ht]
    exact e.adj
  · rintro a b c d ⟨e, _, _, ha, hb⟩ ⟨f, _, _, hc, hd⟩ hac hbd
    obtain ⟨he1, he2⟩ := endpoints ha hb
    obtain ⟨hf1, hf2⟩ := endpoints hc hd
    have hef : e = f := Subtype.ext (Prod.ext (he1.symm.trans (hac.trans hf1))
      (he2.symm.trans (hbd.trans hf2)))
    subst f
    exact ⟨ha.symm.trans hc, hb.symm.trans hd⟩

lemma neighborMass_le (w : V → ℝ) (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop)
    (K : EdgeState G → EdgeState G → ℝ) (hK0 : ∀ a e, 0 ≤ K a e)
    (hK1 : ∀ a, ∑ e, K a e = 1) {L : ℝ} (hL : 0 ≤ L)
    (hadm : ∀ e, good e → w e.dst ≤ L * K (F e) e) (a : EdgeState G) :
    neighborMass (graph F hF good) (w ∘ EdgeState.src) a ≤ L := by
  classical
  let H := graph F hF good
  let N := ↑(neighbors H a)
  have hproj := projection F hF good
  let f : N → EdgeState G := fun b ↦
    ⟨(a.src, b.val.src), hproj.map_adj _ _ ((mem_neighbors _ _ _).1 b.property)⟩
  have hf : Function.Injective f := by
    intro b c heq
    apply Subtype.ext
    apply hproj.neighbor_injective a b.property c.property
    exact congrArg (fun e : EdgeState G ↦ e.dst) heq
  have hle (b : N) : w b.val.src ≤ L * K a (f b) := by
    obtain ⟨e, he, _, ha, hb⟩ := (mem_neighbors H a b.val).1 b.property
    have hef : f b = e := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg EdgeState.src ha).symm.trans (hF e)
      · exact (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    rw [hef, ← ha]
    have hd : b.val.src = e.dst := (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    simpa only [hd] using hadm e he
  calc
    _ = ∑ b : N, w b.val.src := (sum_coe_sort (neighbors H a) (fun b ↦ w b.src)).symm
    _ ≤ ∑ b : N, L * K a (f b) := sum_le_sum (fun b _ ↦ hle b)
    _ = L * ∑ b : N, K a (f b) := (mul_sum _ _ _).symm
    _ ≤ L * ∑ e, K a e := mul_le_mul_of_nonneg_left (sum_injective_le f hf (K a) (hK0 a)) hL
    _ = L := by rw [hK1, mul_one]

/-- All three corner agreements and all six admissible incidences. -/
def Survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) : Prop :=
  F t.edge12 = F t.edge13 ∧
  F t.edge12.rev = F t.edge23 ∧
  F t.edge13.rev = F t.edge23.rev ∧
  good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
  good t.edge23 ∧ good t.edge23.rev

lemma triangleMass_surviving_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (hF : ∀ e, (F e).src = e.src)
    (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) ≤
      6 * triangleMass (graph F hF good) (w ∘ EdgeState.src) := by
  classical
  let H := graph F hF good
  let S := {t : TriangleState G // Survives F good t}
  let f : S → TriangleState H := fun t ↦
    ⟨(F t.val.edge12, F t.val.edge12.rev, F t.val.edge13.rev),
      ⟨t.val.edge12, t.property.2.2.2.1, t.property.2.2.2.2.1, rfl, rfl⟩,
      ⟨t.val.edge13, t.property.2.2.2.2.2.1, t.property.2.2.2.2.2.2.1, t.property.1.symm, rfl⟩,
      ⟨t.val.edge23, t.property.2.2.2.2.2.2.2.1, t.property.2.2.2.2.2.2.2.2,
        t.property.2.1.symm, t.property.2.2.1.symm⟩⟩
  have coords (t : S) :
      (f t).first.src = t.val.first ∧ (f t).second.src = t.val.second ∧
        (f t).third.src = t.val.third := by
    change (F t.val.edge12).src = _ ∧ (F t.val.edge12.rev).src = _ ∧ (F t.val.edge13.rev).src = _
    simp only [hF]
    exact ⟨rfl, rfl, rfl⟩
  have hf : Function.Injective f := by
    intro t s hts
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (coords t).1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.first.src) hts).trans (coords s).1)
    · apply Prod.ext
      · exact (coords t).2.1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.second.src) hts).trans (coords s).2.1)
      · exact (coords t).2.2.symm.trans ((congrArg (fun a : TriangleState H ↦ a.third.src) hts).trans (coords s).2.2)
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight (w ∘ EdgeState.src) (f t) := by
      apply sum_congr rfl
      intro t _
      simp only [TriangleState.weight, Function.comp_apply, (coords t).1, (coords t).2.1, (coords t).2.2]
    _ ≤ ∑ t : TriangleState H, TriangleState.weight (w ∘ EdgeState.src) t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI
