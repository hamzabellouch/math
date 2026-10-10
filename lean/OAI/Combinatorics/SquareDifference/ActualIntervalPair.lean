import OAI.Combinatorics.SquareDifference.IntervalPair

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section FullPair

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma actual_interval_pair (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
    (hHQ : H*(∏j∈B,p j)≤Q)
    (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
    (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j))
    (R : ℝ) (hm₁ : (𝔼 x,intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) x^2)≤R^2)
    (hm₂ : (𝔼 x,intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) x^2)≤R^2)
    (k : ℕ) :
    |tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun x =>
      intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (freezeCoordinates B z (x (cycleVertex k)))*
      intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (freezeCoordinates B w (x (cycleVertex (k+1)))))|≤
      (∏j∈B,p j:ℝ)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
  have hlo := interval_low_pair ps p hinj (fun j => by have := hp j; omega) B a b L N Q H hN hH hab hHQ hD hHn hlarge hcover A hA hfree s t hst z w hzw
  have hhi := frozen_pair_tail p hp B _ _ R hm₁ hm₂ z w H (by exact_mod_cast (show 0<H by omega))
  have hb := squarePair_split_bound (OutsideModulus p B) _ _ (H:ℝ) _ _ hlo hhi
  rw [←tensorGood_frozen_pair p hmass k B z w,Complex.norm_real,Real.norm_eq_abs] at hb
  apply hb.trans_eq
  ring

end FullPair

end SquareDifference

end

end OAI
