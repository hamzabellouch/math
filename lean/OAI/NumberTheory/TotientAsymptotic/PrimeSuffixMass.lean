import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit
import OAI.NumberTheory.TotientAsymptotic.TailHeadCount

namespace OAI

/-! Keep the actual family of suffix products when splitting prime mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem prime_mass_split_suffix {N n : ℕ} (hn : n ≤ N)
    (Q : Finset (Fin N → ℕ)) (T : Finset (Fin (N-n) → ℕ))
    (hT : ∀ p ∈ Q,primeFinal p n ∈ T) :
    (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn),reciprocalShiftWeight p)*
        (∑ p ∈ T,reciprocalShiftWeight p) := by
  classical
  let F := fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)
  have he : (∑ p ∈ Q,reciprocalShiftWeight p) =
      ∑ z ∈ Q.image F,reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun p _ q _ he => prime_parts_injective hn he)]
    exact Finset.sum_congr rfl (fun p _ => reciprocalShiftWeight_split hn p)
  rw [he]
  have hs : Q.image F ⊆ Q.image (fun p => primeInitial p n hn) ×ˢ T := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,hT p hp⟩
  calc
    _ ≤ ∑ z ∈ Q.image (fun p => primeInitial p n hn) ×ˢ T,
        reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun z _ _ => mul_nonneg (reciprocalShiftWeight_nonneg _) (reciprocalShiftWeight_nonneg _))
    _ = _ := by rw [Finset.sum_product]; simp only [←Finset.mul_sum,←Finset.sum_mul]

lemma ordered_prime_family_mass {n : ℕ} (T : Finset (Fin n → ℕ))
    (hT : ∀ p ∈ T,(∀ i,(p i).Prime) ∧ StrictAnti p) :
    (∑ p ∈ T,reciprocalShiftWeight p) =
      ∑ r ∈ T.image (fun p => ∏ i,p i),(r.totient:ℝ)⁻¹ := by
  classical
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun p hp =>
      (prime_tail_totient_weight p (hT p hp).1 (hT p hp).2).symm)
  · intro p hp q hq he
    exact ordered_prime_product_injective (hT p hp).1 (hT q hq).1
      (hT p hp).2 (hT q hq).2 he

end TotientAsymptotic

end

end OAI
