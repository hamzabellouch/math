import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCRT
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCentered

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem centeredProductTransform_eq_zero_of_not_isUnit {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (h : ZMod (∏ i, p i)) (hh : ¬ IsUnit h) :
    centeredProductTransform p hcop S h = 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_crt_zero_coordinate_of_not_isUnit p hp
    (ZMod.prodEquivPi p hcop) h hh
  have hd := dft_crt_product_eq_zero_of_coordinate_zero p (ZMod.prodEquivPi p hcop)
    (fun i x => (Supply.centeredIndicator (S i) x : ℂ))
    (fun i => by rw [← Complex.ofReal_sum, Supply.sum_centeredIndicator]; rfl) h i hi
  change ZMod.dft (fun x => ∏ i, (Supply.centeredIndicator (S i)
    (ZMod.prodEquivPi p hcop x i) : ℂ)) h / (Real.sqrt ((∏ i, p i : ℕ) : ℝ) : ℂ) = 0
  rw [hd, zero_div]

theorem centeredProductTransform_mul_eq_zero_of_not_isUnit {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (c s : ZMod (∏ i, p i)) (hc : ¬ IsUnit c) :
    centeredProductTransform p hcop S (c * s) = 0 :=
  centeredProductTransform_eq_zero_of_not_isUnit p hp hcop S (c * s)
    (fun h => hc (isUnit_of_mul_isUnit_left h))

end Ostmann.QuadraticCenter

end

end OAI
