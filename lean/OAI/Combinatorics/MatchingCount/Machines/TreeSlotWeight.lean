import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Sym2Order
import OAI.Combinatorics.MatchingCount.Machines.TreeBottleneck
import OAI.Combinatorics.MatchingCount.Machines.TreeRationalWeight

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma add_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    add (repr x,repr y)=repr (x+y) := by
  have h:=add_val (repr x) (repr y) x.pos.ne' y.pos.ne'
  rw [val_repr hx,val_repr hy] at h
  unfold add at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma repr_nat (n : ℕ) : repr (n:ℚ)=(n,1) := by simp [repr]

def fuelPower (x : Fraction×List Bool) : Fraction := product (x.2.map (fun _=>x.1))
def fuelPowerRealizer : Realizer fuelPower := composition (mapWith first) productRealizer
lemma polynomial_fuelPower : PolynomialTime fuelPowerRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_first) polynomial_product
lemma fuelPower_repr (q : ℚ) (hq : 0≤q) (fuel : List Bool) :
    fuelPower (repr q,fuel)=repr (q^fuel.length) := by
  unfold fuelPower
  have he : fuel.map (fun _=>repr q)=(fuel.map (fun _=>q)).map repr := by simp
  rw [he,product_repr _ (by intro t ht; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht; exact hq)]
  congr 1
  simp
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped TreeFraction

def tierBase (n : ℕ) : Fraction := add ((1,1),div ((1,1),(n*n,1)))
def tierBaseRealizer : Realizer tierBase := (composition (pair (constant (1,1))
  (composition (pair (constant (1,1)) (pair (composition (pair identity identity) multiply) (constant 1))) divRealizer)) addRealizer).congr (fun _=>rfl)
lemma polynomial_tierBase : PolynomialTime tierBaseRealizer := by
  unfold tierBaseRealizer
  apply polynomial_congr
  have := TreeFraction.polynomial_add
  have := polynomial_div
  tree_cost
lemma tierBase_repr (n : ℕ) : tierBase n=TreeFraction.repr (1+((n:ℚ)^2)⁻¹) := by
  unfold tierBase
  rw [←repr_nat (n*n)]
  have h1 : (1,1)=TreeFraction.repr (1:ℚ) := rfl
  rw [h1,div_repr (by decide) (by positivity),add_repr (by decide) (by positivity)]
  simp only [Nat.cast_mul,one_div,pow_two]

abbrev TierInput := (ℕ×List Bool)×ℕ

def tierPower (x : TierInput) : Fraction :=
  fuelPower (tierBase x.1.1,x.1.2.take (x.1.2.length-x.2))
def tierPowerRealizer : Realizer tierPower := (composition (pair (composition first.fst tierBaseRealizer)
  (composition (pair first.snd (composition (pair (composition first.snd listLength) second) subtract)) takeFast)) fuelPowerRealizer).congr (fun _=>rfl)
lemma polynomial_tierPower : PolynomialTime tierPowerRealizer := by
  unfold tierPowerRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_tierBase
  have := polynomial_takeFast (A:=Bool)
  have := polynomial_fuelPower
  tree_cost
lemma tierPower_repr (n : ℕ) (fuel : List Bool) (r : ℕ) :
    tierPower ((n,fuel),r)=TreeFraction.repr ((1+((n:ℚ)^2)⁻¹)^(fuel.length-r)) := by
  unfold tierPower
  rw [tierBase_repr,fuelPower_repr _ (by positivity),List.length_take,min_eq_left (Nat.sub_le _ _)]

def slotWeight (x : TierInput×Fraction) : Fraction :=
  maximum (div ((1,1),tierPower x.1),minimum (tierPower x.1,x.2))
def slotWeightRealizer : Realizer slotWeight := by
  let P : Realizer (fun x : TierInput×Fraction=>tierPower x.1) := (composition first tierPowerRealizer).congr (fun _=>rfl)
  exact (composition (pair (composition (pair (constant (1,1)) P) divRealizer)
    (composition (pair P second) minimumRealizer)) maximumRealizer).congr (fun _=>rfl)
lemma polynomial_slotWeight : PolynomialTime slotWeightRealizer := by
  unfold slotWeightRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_tierPower
  have := polynomial_div
  have := TreeFraction.polynomial_minimum
  have := TreeFraction.polynomial_maximum
  tree_cost
lemma slotWeight_repr (n : ℕ) (fuel : List Bool) (r : ℕ) (q : ℚ) (hq : 0≤q) :
    slotWeight (((n,fuel),r),TreeFraction.repr q)=TreeFraction.repr
      (max (((1+((n:ℚ)^2)⁻¹)^(fuel.length-r))⁻¹)
        (min ((1+((n:ℚ)^2)⁻¹)^(fuel.length-r)) q)) := by
  unfold slotWeight
  rw [tierPower_repr]
  have h1 : (1,1)=TreeFraction.repr (1:ℚ) := rfl
  rw [h1,div_repr (by decide) (by positivity),minimum_repr (by positivity) hq,
    maximum_repr (by positivity) (le_min (by positivity) hq)]
  simp only [one_div]

lemma slotWeight_source {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V→Finset L} {q : ℕ} (fuel : List Bool) (w : Transport.BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (x : Replica.Ladder.Slot fuel.length q) (e : Transport.BagEdge bags) :
    slotWeight (((Fintype.card V,fuel),Replica.Ladder.rank x),TreeFraction.repr (w e))=
      TreeFraction.repr (Transport.rationalSlotWeight w x e) := by
  exact slotWeight_repr _ _ _ _ (hw e)
end MatchingFPRAS.ExecutableLadder

end OAI
