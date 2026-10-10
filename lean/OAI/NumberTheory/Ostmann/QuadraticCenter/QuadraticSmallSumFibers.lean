import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationSupport

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem prime_square_fiber_card_le_two {p : ℕ} [NeZero p] (hp : p.Prime) (a : ZMod p) :
    ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = a)).card ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let F := (Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = a)
  by_cases hF : F.Nonempty
  · obtain ⟨x, hx⟩ := hF
    have hx' : x ^ 2 = a := (Finset.mem_filter.mp hx).2
    have hsub : F ⊆ {x, -x} := by
      intro y hy
      have hy' : y ^ 2 = a := (Finset.mem_filter.mp hy).2
      rcases eq_or_eq_neg_of_sq_eq_sq y x (hy'.trans hx'.symm) with h | h <;>
        simp [h]
    exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using Finset.card_insert_le x {-x})
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [F] at this
    simp [this]

theorem prime_product_square_fiber_card_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ZMod (∏ i, p i)) :
    ((Finset.univ : Finset (ZMod (∏ i, p i))).filter (fun x => x ^ 2 = a)).card ≤
      2 ^ Fintype.card ι := by
  classical
  let e := ZMod.prodEquivPi p hcop
  let R := fun i => (Finset.univ : Finset (ZMod (p i))).filter (fun x => x ^ 2 = e a i)
  calc
    _ ≤ (Fintype.piFinset R).card := by
      apply Finset.card_le_card_of_injOn e
      · intro x hx
        change e x ∈ Fintype.piFinset R
        apply Fintype.mem_piFinset.mpr
        intro i
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hx' := (Finset.mem_filter.mp hx).2
        have he := congrArg (fun z => e z i) hx'
        simpa only [map_pow, Pi.pow_apply] using he
      · intro x hx y hy hxy
        exact e.injective hxy
    _ = ∏ i, (R i).card := Fintype.card_piFinset R
    _ ≤ ∏ _i : ι, 2 := by
      apply Finset.prod_le_prod
      intro i _
      exact prime_square_fiber_card_le_two (hp i) (e a i)
    _ = _ := by simp

theorem prime_product_scaled_square_fiber_card_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (c a : ZMod (∏ i, p i)) (hc : IsUnit c) :
    ((Finset.univ : Finset (ZMod (∏ i, p i))).filter (fun x => c * x ^ 2 = a)).card ≤
      2 ^ Fintype.card ι := by
  classical
  obtain ⟨u, rfl⟩ := hc
  have heq : ((Finset.univ : Finset (ZMod (∏ i, p i))).filter
      (fun x => (u : ZMod (∏ i, p i)) * x ^ 2 = a)) =
      Finset.univ.filter (fun x => x ^ 2 = (↑u⁻¹ : ZMod (∏ i, p i)) * a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  rw [heq]
  exact prime_product_square_fiber_card_le p hp hcop _

end Ostmann.QuadraticCenter

end

end OAI
