import OAI.NumberTheory.CubicMoment.Estimates.PrimeComplementFibers

namespace OAI

/-! Nonnegative uncollected tuple weights. These retain the absolute
complementary mass; no cancellation of collected coefficients is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complementAbsoluteWeight (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (r : Eisenstein) : ℝ :=
  ∑ g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r),
    ∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖

lemma complementAbsoluteWeight_nonneg (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (r : Eisenstein) :
    0 ≤ complementAbsoluteWeight S i W r :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _))

lemma complementAbsoluteWeight_bound (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1) (r : Eisenstein) :
    complementAbsoluteWeight S i W r ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold complementAbsoluteWeight
  calc
    _ ≤ ∑ _g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgs := (coordinateComplement_mem S i g).mp (Finset.mem_filter.mp hg).1
      apply Finset.prod_le_one₀ (fun _ _ => _root_.norm_nonneg _)
      intro j hj
      exact hW j (g j) (hgs.2 j (Finset.mem_erase.mp hj).1)
    _ = (((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card:ℝ) := by simp
    _ ≤ _ := Nat.cast_le.mpr (complementTuple_fiber_card S hS i r)

lemma complementAbsoluteWeight_rough (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) {w : ℝ}
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {r p : Eisenstein} (hr : complementAbsoluteWeight S i W r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w ≤ norm p := by
  obtain ⟨g,hg,hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  obtain ⟨hg,hgr⟩ := Finset.mem_filter.mp hg
  have hpd : p ∣ ∏ j, g j := by rw [hgr]; exact hpr
  obtain ⟨j,hji,hpj⟩ := complementTuple_prime_factor S hS i hg hp hpd
  have hnorm : ‖W j (g j)‖ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩)
  have hWj : W j (g j) ≠ 0 := norm_ne_zero_iff.mp hnorm
  rw [hpj]
  exact hrough j hji (g j) (((coordinateComplement_mem S i g).mp hg).2 j hji) hWj

end CubicFirstMoment

end

end OAI
