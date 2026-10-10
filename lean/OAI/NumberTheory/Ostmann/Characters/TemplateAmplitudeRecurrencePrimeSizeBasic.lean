import Mathlib.Algebra.BigOperators.Associated
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem primeProductPrior_mem_of_mass_ne_zero {I : Type*} [Fintype I] {Q : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (x : I → PrimeUpTo Q)
    (hx : (productPrior (fun i => primeShellPrior (E i) (hE i))).mass x ≠ 0)
    (i : I) : x i ∈ E i := by
  by_contra hi
  apply hx
  change (∏ i, (primeShellPrior (E i) (hE i)).mass (x i)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [primeShellPrior_mass,ite_eq_right hi,zero_div]

theorem prime_factor_sampleProduct {I : Type*} [Fintype I] {Q q : ℕ}
    (x : I → PrimeUpTo Q) (hq : q.Prime)
    (hd : q ∣ (∏ i, ((x i).val : ℤ)).natAbs) : ∃ i, q = (x i).val := by
  have hd' : q ∣ ∏ i, (x i).val := by
    simpa only [← Nat.cast_prod,Int.natAbs_natCast] using hd
  obtain ⟨i,hi,hdiv⟩ := ((Nat.prime_iff.mp hq).dvd_finsetProd_iff (fun i => (x i).val)).mp hd'
  exact ⟨i,((primeUpTo_prime (x i)).dvd_iff_eq hq.ne_one).mp hdiv |>.symm⟩

theorem prime_factor_sampleProduct_gt {I : Type*} [Fintype I] {Q V q : ℕ}
    (x : I → PrimeUpTo Q) (hx : ∀ i, V < (x i).val) (hq : q.Prime)
    (hd : q ∣ (∏ i, ((x i).val : ℤ)).natAbs) : V < q := by
  obtain ⟨i,rfl⟩ := prime_factor_sampleProduct x hq hd
  exact hx i

theorem primeProductPrior_prime_gt {I : Type*} [Fintype I] {Q V : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hV : ∀ i p, p ∈ E i → V < p.val) (x : I → PrimeUpTo Q)
    (hx : (productPrior (fun i => primeShellPrior (E i) (hE i))).mass x ≠ 0)
    (i : I) : V < (x i).val :=
  hV i (x i) (primeProductPrior_mem_of_mass_ne_zero E hE x hx i)

end Ostmann.Characters.Template

end

end OAI
