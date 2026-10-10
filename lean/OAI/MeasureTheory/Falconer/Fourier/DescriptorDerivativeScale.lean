import OAI.MeasureTheory.Falconer.Estimates.GlobalDescriptorBounds
import OAI.MeasureTheory.Falconer.Measures.MaskProductBudget
import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # A uniform derivative scale for the actual descriptor family

The fixed derivative constants and polynomial list size are absorbed before
choosing any cells, net points or descriptor family. The retained scale
remembers the largest nominal descriptor length.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def descriptorDerivativeScale (N : ℕ) (σ : ℝ) (L : ℕ) : ℝ :=
  ((2:ℝ)^N)^σ * max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))

theorem descriptorDerivativeScale_ge_one (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) :
    1 ≤ descriptorDerivativeScale N σ L := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) hσ
  · exact le_max_left _ _

theorem descriptorMaskRadius_inv_eq (N : ℕ) (σ : ℝ) (b : PlanarFalconer.PolicyDescriptor) :
    (descriptorMaskRadius N σ b)⁻¹ =
      8*max 1 ((2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(-50*σ)) := by
  let t : ℝ := 1/(2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(50*σ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hi : t⁻¹ = (2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(-50*σ) := by
    rw [show -50*σ = -(50*σ) by ring,Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^N)]
    simp only [t,mul_inv_rev,one_div,inv_inv]
    ring
  change (min 1 t/8)⁻¹ = _
  rw [inv_div]
  by_cases h : t ≤ 1
  · rw [min_eq_right h,← hi,max_eq_right ((one_le_inv₀ ht).mpr h),div_eq_mul_inv]
  · rw [min_eq_left (le_of_not_ge h),← hi,max_eq_left ((inv_le_one₀ ht).mpr (le_of_not_ge h))]
    norm_num

theorem descriptorMaskRadius_inv_le (N : ℕ) (σ : ℝ)
    (b : PlanarFalconer.PolicyDescriptor) {L : ℕ} (hL : PlanarFalconer.descriptorLength b ≤ L) :
    (descriptorMaskRadius N σ b)⁻¹ ≤
      8*max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ)) := by
  rw [descriptorMaskRadius_inv_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hL) (by positivity))

theorem uniform_descriptor_global_scale (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (f : ℝ → ℝ) (J i L : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
      (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      B.card ≤ (N+1)^P → (∀ b ∈ B, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w => (descriptorAmbientProduct Q ρ f N σ J i B S x w : ℂ)) z‖ ≤
          (descriptorDerivativeScale N σ L)^k := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientProduct_complex_global_budget d K
  obtain ⟨N₁,hcount⟩ := descriptor_count_subpower P (half_pos hσ)
  obtain ⟨N₂,hconst⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) (8*C)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q ρ f J i L B S hcard hlength hsep x z k hk
  let W := max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))
  have hW : 0 ≤ W := (zero_le_one.trans (le_max_left _ _))
  have hc := hcount N ((le_max_left _ _).trans hN) B hcard
  have hC' := hconst N ((le_max_right _ _).trans hN)
  have hs : (B.card:ℝ)*C*(8*W) ≤ descriptorDerivativeScale N σ L := by
    calc
      _ = ((B.card:ℝ)*(8*C))*W := by ring
      _ ≤ (((2:ℝ)^N)^(σ/2)*((2:ℝ)^N)^(σ/2))*W :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc hC' (by positivity) (by positivity)) hW
      _ = descriptorDerivativeScale N σ L := by
        rw [← Real.rpow_add (by positivity),show σ/2+σ/2 = σ by ring]
        rfl
  have hb := hbound Q ρ f N σ J i B S (8*W) (by positivity) hsep
    (fun b hb => descriptorMaskRadius_inv_le N σ b (hlength b hb)) x z k hk
  exact hb.trans (pow_le_pow_left₀ (by positivity) hs k)

end Falconer

end OAI
