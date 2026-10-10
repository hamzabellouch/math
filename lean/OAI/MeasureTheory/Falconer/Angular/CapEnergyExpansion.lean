import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-!
# Inserting the actual cap partition before localization

The complex cross terms remain inside the angular and radial integrals.
The cap insertion is an exact identity; no positivity or pointwise
truncation is used to discard an oscillatory term.
-/

namespace Falconer
open MeasureTheory

theorem cap_pair_partition {d : ℕ} {κ : Type*} (K : Finset κ)
    (η : κ → Sphere d → ℝ) (hpart : ∀ w, ∑ k ∈ K, η k w = 1)
    (w₁ w₂ : Sphere d) : ∑ k ∈ K ×ˢ K, η k.1 w₁*η k.2 w₂ = 1 := by
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hpart,hpart,one_mul]

theorem cap_partition_cross_sum {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (K : Finset κ) (η : κ → Sphere d → ℝ)
    (hpart : ∀ w, ∑ k ∈ K, η k w = 1) (F : ι → ℂ) (w₁ w₂ : Sphere d) :
    (∑ i ∈ S, ∑ j ∈ S, F i*star (F j)) =
      ∑ k ∈ K ×ˢ K, ∑ i ∈ S, ∑ j ∈ S,
        (η k.1 w₁*η k.2 w₂) • (F i*star (F j)) := by
  simp_rw [← Finset.smul_sum]
  rw [← Finset.sum_smul,cap_pair_partition K η hpart,one_smul]

theorem integrated_cap_cross_expansion {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (K : Finset κ) (η : κ → Sphere d → ℝ)
    (hpart : ∀ w, ∑ k ∈ K, η k w = 1)
    (F : ι → (ℝ × (Sphere d × Sphere d)) → ℂ) (v : ℝ) (Ψ : ℝ → ℝ) :
    (∫ z, ∑ i ∈ S, ∑ j ∈ S, F i z*star (F j z) ∂angularProductMeasure d v Ψ) =
      ∫ z, ∑ k ∈ K ×ˢ K, ∑ i ∈ S, ∑ j ∈ S,
        (η k.1 z.2.1*η k.2 z.2.2) • (F i z*star (F j z))
        ∂angularProductMeasure d v Ψ := by
  apply integral_congr_ae
  filter_upwards with z
  exact cap_partition_cross_sum S K η hpart (fun i => F i z) z.2.1 z.2.2

end Falconer

end OAI
