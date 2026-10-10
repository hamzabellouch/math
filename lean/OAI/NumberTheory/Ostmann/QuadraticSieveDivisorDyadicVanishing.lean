import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationProduct
import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Finset

theorem product_divisor_row_eq_zero_of_large {N d : ℕ} (S T : Finset ℕ)
    (a b : ℕ → ℂ) (m : ℤ) (hd : N^2<d)
    (hS : S⊆oddSquarefreeUpTo N) (hT : T⊆oddSquarefreeUpTo N) :
    coprimeProductDivisorJacobiRow S T a b d m=0 := by
  unfold coprimeProductDivisorJacobiRow
  apply sum_eq_zero
  intro n hn
  apply sum_eq_zero
  intro t ht
  apply ite_eq_right
  intro hdiv
  obtain ⟨hn0,hnN,hnodd,hnsq⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  obtain ⟨ht0,htN,htodd,htsq⟩ := mem_oddSquarefreeUpTo.mp (hT ht)
  have hle := Nat.le_of_dvd (Nat.mul_pos hn0 ht0) hdiv.2
  have hprod := Nat.mul_le_mul hnN htN
  nlinarith

theorem product_divisor_annulus_eq_zero_of_large {D N : ℕ} (V S T : Finset ℕ)
    (a b : ℕ → ℂ) (hD : N^2<D)
    (hS : S⊆oddSquarefreeUpTo N) (hT : T⊆oddSquarefreeUpTo N) :
    (∑ d∈Ioc D (2*D),∑ v∈V,‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖)=0 := by
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro v hv
  rw [product_divisor_row_eq_zero_of_large S T a b (v : ℤ)
    (hD.trans (mem_Ioc.mp hd).1) hS hT,norm_zero]

end Ostmann.QuadraticSieve

end

end OAI
