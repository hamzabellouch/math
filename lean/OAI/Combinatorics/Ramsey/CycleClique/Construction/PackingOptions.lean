import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules
import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallGrowth
import OAI.Combinatorics.Ramsey.CycleClique.Construction.IndependentPacking

namespace OAI

/-! Soundness of the manuscript's weighted packing test. Radius index zero
denotes a singleton; index `r+1` denotes its exterior radius-`r` ball. -/

namespace CycleClique.Construction
variable {V : Type*} [Fintype V]

noncomputable def packingRegion (G : SimpleGraph V) (X : Finset V)
    (x : V) : ℕ → Finset V
  | 0 => {x}
  | r + 1 => outsideBallFinset G X x r

def PackingCompatible (G : SimpleGraph V) (X : Set V) (x : V) (r : ℕ) (y : V) (s : ℕ) : Prop :=
  if r = 0 ∧ s = 0 then ¬ OutsidePath G X x y 0
  else ∀ d, 1 ≤ d → d ≤ r + s → ¬ OutsidePath G X x y d

omit [Fintype V] in
theorem PackingCompatible.symm {G : SimpleGraph V} {X : Set V} {x y : V} {r s : ℕ}
    (h : PackingCompatible G X x r y s) : PackingCompatible G X y s x r := by
  unfold PackingCompatible at *
  by_cases hzero : r = 0 ∧ s = 0
  · have hzero' : s = 0 ∧ r = 0 := hzero.symm
    simp only [hzero] at h
    simp only [hzero']
    exact fun hp => h hp.reverse
  · have hzero' : ¬ (s = 0 ∧ r = 0) := fun hs => hzero hs.symm
    simp only [hzero, ↓reduceIte] at h
    simp only [hzero', ↓reduceIte]
    intro d hd hbound hp
    exact h d hd (by omega) hp.reverse

/-- Compatibility gives both vertex disjointness and anticompleteness,
with the singleton case handled separately from positive intervals. -/
theorem packingRegions_separated {G : SimpleGraph V} {X : Finset V} {x y : V} {r s : ℕ}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hcompat : PackingCompatible G (X : Set V) x r y s) :
    Disjoint (packingRegion G X x r) (packingRegion G X y s) ∧
    ∀ u ∈ packingRegion G X x r, ∀ v ∈ packingRegion G X y s, ¬ G.Adj u v := by
  classical
  cases r with
  | zero =>
    cases s with
    | zero =>
      have hnon : ¬ G.Adj x y := by
        have h := hcompat
        simp only [PackingCompatible, and_self, ↓reduceIte] at h
        exact fun hadj => h (outsidePath_zero.mpr hadj)
      constructor
      · simpa [packingRegion] using hxy
      · simpa [packingRegion] using hnon
    | succ s =>
      have hf : ∀ d, 1 ≤ d → d ≤ s + 1 →
          ¬ PositiveOutsidePath G (X : Set V) y x d := by
        intro d hd hds hp
        have hc := hcompat.symm
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte,
          Nat.add_zero] at hc
        exact hc d hd hds hp.toOutside
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hv hball
        have he : v = x := by simpa [packingRegion] using hv
        subst v
        exact (mem_outsideBallFinset.mp hball).1 hx
      · intro u hu v hv hadj
        have he : u = x := by simpa [packingRegion] using hu
        subst u
        exact singleton_outside_ball_separated hy hx hxy.symm hf v
          (mem_outsideBallFinset.mp hv) hadj.symm
  | succ r =>
    cases s with
    | zero =>
      have hf : ∀ d, 1 ≤ d → d ≤ r + 1 →
          ¬ PositiveOutsidePath G (X : Set V) x y d := by
        intro d hd hds hp
        have hc := hcompat
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte,
          Nat.add_zero] at hc
        exact hc d hd hds hp.toOutside
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hball hv
        have he : v = y := by simpa [packingRegion] using hv
        subst v
        exact (mem_outsideBallFinset.mp hball).1 hy
      · intro u hu v hv hadj
        have he : v = y := by simpa [packingRegion] using hv
        subst v
        exact singleton_outside_ball_separated hx hy hxy hf u
          (mem_outsideBallFinset.mp hu) hadj
    | succ s =>
      have hf : ∀ d, 1 ≤ d → d ≤ r + s + 2 →
          ¬ PositiveOutsidePath G (X : Set V) x y d := by
        intro d hd hds hp
        have hc := hcompat
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte] at hc
        exact hc d hd (by omega) hp.toOutside
      obtain ⟨hdis, hanti⟩ := outside_balls_separated hx hy hxy hf
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hv hw
        exact Set.disjoint_left.mp hdis (mem_outsideBallFinset.mp hv)
          (mem_outsideBallFinset.mp hw)
      · intro u hu v hv
        exact hanti u (mem_outsideBallFinset.mp hu) v (mem_outsideBallFinset.mp hv)

/-- The weights of every compatible family with distinct bases sum to
at most the ambient independence bound. -/
theorem packing_test {ι : Type*} [Fintype ι] {G : SimpleGraph V} {k : ℕ}
    (hbound : IndependenceBound G k) (X : Finset V)
    (base : ι → V) (radius weight : ι → ℕ)
    (hbase : Function.Injective base) (hX : ∀ i, base i ∈ X)
    (hweight : ∀ i, HasIndependent (G.induce (packingRegion G X (base i) (radius i) : Set V))
      (weight i))
    (hcompat : ∀ i j, i ≠ j →
      PackingCompatible G (X : Set V) (base i) (radius i) (base j) (radius j)) :
    ∑ i, weight i ≤ k := by
  classical
  choose I hIsub hIind hIcard using fun i => exists_independent_subset (hweight i)
  have hsep := fun i j hij => packingRegions_separated (hX i) (hX j)
    (fun h => hij (hbase h)) (hcompat i j hij)
  have hdis : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint I := by
    intro i _ j _ hij
    exact (hsep i j hij).1.mono (hIsub i) (hIsub j)
  have hanti : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      ∀ u ∈ I i, ∀ v ∈ I j, ¬ G.Adj u v := by
    intro i _ j _ hij u hu v hv
    exact (hsep i j hij).2 u (hIsub i hu) v (hIsub j hv)
  have h := independent_packing hbound Finset.univ I (fun i _ => hIind i) hdis hanti
  simpa only [hIcard] using h

end CycleClique.Construction

end OAI
