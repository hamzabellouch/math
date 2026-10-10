import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalUnitInput
import OAI.Combinatorics.KMedian.Geometry.RationalSplitEnumeration

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset
variable {f j : ℕ}

 theorem cost_assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hx0 : ∀ c i, 0≤x c i) (dc : Fin j → Fin f → ℚ) (c : Fin j) :
    (∑ a ∈ assigned y x c, weights y x a*dc c (original y x a))=∑ i, x c i*dc c i := by
  change (∑ a ∈ assigned y x c, (fun a : Piece y x => weight y x a*dc c a.1) (index y x a))=_
  rw [assigned_sum y x c (fun a : Piece y x => weight y x a*dc c a.1)]
  have hh := cost_assignment y x hx0 c (fun i => (dc c i:ℝ))
  exact_mod_cast hh

 theorem nearest_rational (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hx1 : ∀ c i, x c i≤y i) (dc : Fin j → Fin f → ℚ)
    (horder : ∀ c a b, 0<x c a → x c b<y b → dc c a≤dc c b)
    (c : Fin j) (a : Fin (count y x)) (ha : a∈assigned y x c)
    (b : Fin (count y x)) (hb : b∉assigned y x c) :
    dc c (original y x a)≤dc c (original y x b) := by
  have hh := nearest_assignment y x hx1 (fun c a => (dc c a:ℝ))
    (fun c a b ha hb => by exact_mod_cast horder c a b ha hb)
    c (index y x a) ((mem_assigned y x c a).mp ha) (index y x b)
    (fun hh => hb ((mem_assigned y x c b).mpr hh))
  exact_mod_cast hh

def input (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (_ : ∀ i, 0≤y i) (hy1 : ∀ i, y i≤1)
    (hx0 : ∀ c i, 0≤x c i) (hx1 : ∀ c i, x c i≤y i) (hxu : ∀ c, ∑ i, x c i=1)
    (hdc : ∀ c a, 0≤dc c a) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (horder : ∀ c a b, 0<x c a → x c b<y b → dc c a≤dc c b) : RationalUnitInput (count y x) j where
  y := weights y x
  F := assigned y x
  dc := fun c a => dc c (original y x a)
  dd := dd
  df := fun a b => df (original y x a) (original y x b)
  hy := fun a => weight_pos y x (index y x a)
  hy1 := fun a => (weight_le y x hx1 (index y x a)).trans (hy1 (original y x a))
  hu := fun c => (assigned_sum y x c (weight y x)).trans ((sum_assignment y x hx0 c).trans (hxu c))
  hdc := fun c a => hdc c (original y x a)
  hdd := hdd
  hsymm := hds
  hnear := nearest_rational y x hx1 dc horder

 theorem input_cost (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hy1 : ∀ i, y i≤1)
    (hx0 : ∀ c i, 0≤x c i) (hx1 : ∀ c i, x c i≤y i) (hxu : ∀ c, ∑ i, x c i=1)
    (hdc : ∀ c a, 0≤dc c a) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (horder : ∀ c a b, 0<x c a → x c b<y b → dc c a≤dc c b) (c : Fin j) :
    (input y x dc dd df hy hy1 hx0 hx1 hxu hdc hdd hds horder).V c=∑ i, x c i*dc c i :=
  cost_assigned y x hx0 dc c

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
