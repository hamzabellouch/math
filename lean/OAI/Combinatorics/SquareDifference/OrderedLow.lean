import OAI.Combinatorics.SquareDifference.BlockAverage

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma kernelAbsoluteConstant_nonneg : 0≤kernelAbsoluteConstant := by
  unfold kernelAbsoluteConstant
  positivity

section Low

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma tensorGood_pair_uniform (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H T : ℕ) (hN : 1≤N) (hH : 1≤H) (hT : 1≤T)
    (hHQ : H*T^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(T^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ)
    (hm : ∀v,(𝔼 x,intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)) x^2)≤R^2)
    (B : Finset J) (hB : (∏j∈B,p j)≤T^(Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1)))))
    (z : TupleVertex → ResidueSpace p) (hz : lawDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) z≠0) :
    |tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun x =>
      intervalLift p (a (cycleVertex k)) L Q (smallResidueInput (smallModulus ps) A (s (cycleVertex k)))
        (freezeCoordinates B (z (cycleVertex k)) (x (cycleVertex k)))*
      intervalLift p (a (cycleVertex (k+1))) L Q (smallResidueInput (smallModulus ps) A (s (cycleVertex (k+1))))
        (freezeCoordinates B (z (cycleVertex (k+1))) (x (cycleVertex (k+1)))))|≤
      (T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
  have hc := otherVertices_card (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k)
  have hq : (∏j∈B,p j)≤T^(Fintype.card TupleVertex) :=
    hB.trans (Nat.pow_le_pow_right hT (by omega))
  have hq' : (∏j∈B,p j:ℝ)≤(T:ℝ)^(Fintype.card TupleVertex) := by exact_mod_cast hq
  have hDB : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000) := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg (smallModulus ps))).trans hD
  have hsq := tensorGood_density_square p hmass k z hz
  have hb := actual_interval_pair ps p hinj hp hmass B _ _ L N Q H hN hH hab
    ((Nat.mul_le_mul_left H hq).trans hHQ) hDB hHn hlarge hcover A hA hfree
    _ _ hst _ _ (fun j _ => hsq j) R (hm _) (hm _) k
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hq' (Real.rpow_nonneg (Nat.cast_nonneg H) _))
    (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))

lemma ordered_low_bound (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H T : ℕ) (hN : 1≤N) (hH : 1≤H) (hT : 1≤T)
    (hHQ : H*T^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(T^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ)
    (hm : ∀v,(𝔼 x,intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)) x^2)≤R^2) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (retainedIntervalLift p a L Q T {cycleVertex k,cycleVertex (k+1)}
        (fun v => smallResidueInput (smallModulus ps) A (s v)))|≤
      ((smallModulus ps:ℝ)*(T:ℝ)^2)^(Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1))))*
      ((T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2)) := by
  have hinjp : Function.Injective p := fun x y h => Sum.inr_injective (hinj h)
  have he : 0≤(T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
      (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))
  have hb := interval_low_product_bound p hinjp (fun j => tupleGoodLaw (p:=p j))
    (fun _ => tupleGoodLaw_nonneg) (fun j => tupleGoodLaw_probability (hmass j))
    (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k) a L
    (fun v => smallResidueInput (smallModulus ps) A (s v)) (smallModulus ps) (Nat.cast_nonneg _)
    (fun _ n => smallResidueInput_bound _ _ _ n) T _ (filteredFamily_card p hinjp Q T)
    (fun U hU => (mem_filter.mp hU).2) _ _ _ he
    (tensorGood_pair_uniform ps p hinj hp hmass a L N Q H T hN hH hT hHQ hD hHn hlarge hcover A hA hfree s k hab hst R hm)
  convert hb using 1
  congr 2
  funext w
  exact retainedInterval_pair p a L Q T _ _ (cycleVertex_consecutive_ne k) _ w

end Low

end SquareDifference

end

end OAI
