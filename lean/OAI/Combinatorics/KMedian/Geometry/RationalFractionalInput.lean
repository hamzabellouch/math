import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ApproximateLPSelection
import OAI.Combinatorics.KMedian.Geometry.RationalSplitInput

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

 theorem computedNearest_ordered (y d : Fin f → ℚ) (hy : ∀ i, 0≤y i) (hm : 1≤∑ i, y i)
    (a b : Fin f) (ha : 0<(computedNearest y d hy hm)[a.val])
    (hb : (computedNearest y d hy hm)[b.val]<y b) : d a≤d b := by
  simp only [computedNearest,Vector.getElem_ofFn] at ha hb
  exact (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).ordered a (mem_univ _)
    b (mem_univ _) ha hb

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

def y (i : Fin f) : ℚ := a.opening[i.val]

include ha hj in
theorem mass_one : 1≤∑ i, y a i := by
  let c : Fin j := ⟨0,hj⟩
  calc
    1 = ∑ i : Fin f, a.assignment[c.val][i.val] := (ha.2.2.1 c).symm
    _ ≤ ∑ i, y a i := sum_le_sum (fun i _ => (ha.2.1 c i).2)

def x (dc : Fin j → Fin f → ℚ) (c : Fin j) (i : Fin f) : ℚ :=
  (computedNearest (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj))[i.val]

 theorem x_spec (dc : Fin j → Fin f → ℚ) :
    (∀ c i, 0≤x a k ha hj dc c i ∧ x a k ha hj dc c i≤y a i) ∧
    (∀ c, ∑ i, x a k ha hj dc c i=1) ∧
    (∀ c b b', 0<x a k ha hj dc c b → x a k ha hj dc c b'<y a b' → dc c b≤dc c b') ∧
    (∑ c, ∑ i, x a k ha hj dc c i*dc c i)≤a.value dc := by
  have hs := fun c => computedNearest_spec (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) 0
  refine ⟨fun c => (hs c).1,fun c => (hs c).2.1,?_,?_⟩
  · intro c b b' hb hb'
    exact computedNearest_ordered (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) b b' hb hb'
  · apply sum_le_sum
    intro c _
    change (∑ i : Fin f, (computedNearest (y a) (dc c) _ _)[i.val]*dc c i)≤_
    rw [(hs c).2.2]
    exact FractionalDual.value_le_assignment (dc c) (y a) (fun i => a.assignment[c.val][i.val]) 0
      (ha.2.1 c) (ha.2.2.1 c)

def count (dc : Fin j → Fin f → ℚ) : ℕ :=
  RationalSplitting.count (y a) (x a k ha hj dc)

def original (dc : Fin j → Fin f → ℚ) : Fin (count a k ha hj dc) → Fin f :=
  RationalSplitting.original (y a) (x a k ha hj dc)

def unitInput (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    RationalUnitInput (count a k ha hj dc) j :=
  let hs := x_spec a k ha hj dc
  RationalSplitting.input (y a) (x a k ha hj dc) dc dd df (fun i => (ha.1 i).1) (fun i => (ha.1 i).2)
    (fun c i => (hs.1 c i).1) (fun c i => (hs.1 c i).2) hs.2.1 hdc hdd hds hs.2.2.1

 theorem input_mass (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    (∑ b, (unitInput a k ha hj dc dd df hdc hdd hds).y b)≤(k:ℚ)+1 := by
  change (∑ b, RationalSplitting.weights (y a) (x a k ha hj dc) b)≤_
  exact (RationalSplitting.weights_sum (y a) (x a k ha hj dc) (fun i => (ha.1 i).1)
    (fun c i => ((x_spec a k ha hj dc).1 c i).2)).trans_le ha.2.2.2

 theorem input_cost (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    (∑ c, (unitInput a k ha hj dc dd df hdc hdd hds).V c)≤a.value dc := by
  have he : ∀ c, (unitInput a k ha hj dc dd df hdc hdd hds).V c=
      ∑ i, x a k ha hj dc c i*dc c i := fun c => RationalSplitting.cost_assigned (y a) (x a k ha hj dc)
        (fun c i => ((x_spec a k ha hj dc).1 c i).1) dc c
  simp_rw [he]
  exact (x_spec a k ha hj dc).2.2.2

 def realization {X : Type} [PseudoMetricSpace X]
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (c : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c' b, dist (c c') (i b)=(dc c' b:ℝ))
    (hcc : ∀ c' c'', dist (c c') (c c'')=(dd c' c'':ℝ)) :
    (unitInput a k ha hj dc dd df hdc hdd hds).Realization X where
  i := fun b => i (original a k ha hj dc b)
  c := c
  hdf := fun first second => hdf (original a k ha hj dc first) (original a k ha hj dc second)
  hdc := fun client piece => hc client (original a k ha hj dc piece)
  hdd := hcc

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
