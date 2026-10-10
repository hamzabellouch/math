import OAI.NumberTheory.Jacobsthal.Sieve.FullPatternCongruences

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosHyperbolaError
attribute [local instance] Classical.propDecidable

theorem mem_open_closed_integer_interval (x y : ℝ) (n : ℤ) :
    n ∈ realIntervalIntegers x y false true ↔ x < (n : ℝ) ∧ (n : ℝ) ≤ y := by
  simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
    Bool.false_eq_true,ite_false,ite_true]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.le,h.2⟩,h⟩

theorem mem_closed_open_integer_interval (x y : ℝ) (n : ℤ) :
    n ∈ realIntervalIntegers x y true false ↔ x ≤ (n : ℝ) ∧ (n : ℝ) < y := by
  simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
    Bool.false_eq_true,ite_false,ite_true]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1,h.2.le⟩,h⟩

theorem original_pair_mem_sourcePairs (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H)
    (x0 x1 y0 y1 : ℝ) (hp : x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1)
    (hm : y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    ((p.val : ℤ),primeM P H C0 hP p) ∈
      sourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) 1 x0 x1 y0 y1 false true true false := by
  dsimp only
  have hres := full_pattern_residue_congruences P w H C0 hw hP hlarge p
  have hprod := full_pattern_product_congruence P w H C0 hw hP hlarge p
  unfold sourcePairs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,by simp only [Nat.cast_one,one_dvd,true_and];exact ⟨hres.1,hres.2.1,hres.2.2,hprod⟩⟩
  · exact (mem_open_closed_integer_interval x0 x1 (p.val : ℤ)).mpr (by exact_mod_cast hp)
  · exact (mem_closed_open_integer_interval y0 y1 (primeM P H C0 hP p)).mpr hm

theorem original_prime_pair_injective (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime) :
    Function.Injective (fun p : goodPrimes P H => ((p.val : ℤ),primeM P H C0 hP p)) := by
  intro p q he
  apply Subtype.ext
  have hh : (p.val : ℤ) = (q.val : ℤ) := congrArg Prod.fst he
  exact Int.ofNat.inj hh

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
