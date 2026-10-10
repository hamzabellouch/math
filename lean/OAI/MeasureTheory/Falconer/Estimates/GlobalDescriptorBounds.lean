import OAI.MeasureTheory.Falconer.Angular.GlobalCapBounds
import OAI.MeasureTheory.Falconer.Measures.AmbientProduct
import OAI.MeasureTheory.Falconer.Measures.AmbientMaskProductBudget

namespace OAI

/-! # Global derivative budgets for actual descriptor products

The constants are chosen before the scale, cells, descriptor list and cap
families.  The only list-size loss is a power of its cardinality.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer

theorem descriptorAmbientMask_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (x w : Space d),
        ‖iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w‖ ≤
          C*((descriptorMaskRadius N σ b)⁻¹)^k := by
  obtain ⟨C,hC,hCb⟩ := capCutoffAmbient_global_derivatives d k
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep x w
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
      ((mem_cubePaths d _ p).mp hp) hxp)
    rw [he]
    exact hCb _ (descriptorMaskRadius_pos N σ b) S hsep _ w
  · rw [descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)

theorem descriptorAmbientMask_global_bounds {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (x z : Space d) :
    0 ≤ descriptorAmbientMask Q ρ m N σ J i b S x z ∧
      descriptorAmbientMask Q ρ m N σ J i b S x z ≤ 1 := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
      ((mem_cubePaths d _ p).mp hp) hxp]
    exact capCutoffAmbient_global_bounds (descriptorMaskRadius_pos N σ b) S _ z
  · rw [descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx]
    exact ⟨le_rfl,zero_le_one⟩

theorem descriptorAmbientProduct_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  classical
  choose A hA hAb using fun k => descriptorAmbientMask_global_derivatives d k
  let C := 1+∑ k ∈ Finset.range (K+1), A k
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (K+1)) => hA k)]
  have hAC (k : ℕ) (hk : k ≤ K) : A k ≤ C := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.range (K+1)) => hA k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z
  apply ambient_mask_product_budget B
    (fun b => descriptorAmbientMask Q ρ m N σ J i b (S b) x) hC hD K z
  · exact fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x
  · intro b _
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b (S b) x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · intro b hb k _ hk
    apply (hAb k Q ρ m N σ J i b (S b) (hsep b hb) x z).trans
    exact mul_le_mul (hAC k hk)
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) (hscale b hb) k)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)
      (zero_le_one.trans hC)

theorem descriptorAmbientProduct_complex_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w =>
          (descriptorAmbientProduct Q ρ m N σ J i B S x w : ℂ)) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  obtain ⟨C,hC,hCb⟩ := descriptorAmbientProduct_global_budget d K
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z k hk
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((descriptorAmbientProduct_contDiff Q ρ m N σ J i B S x).contDiffAt (x := z))
    (by simp : (k : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘
    descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤ _
  rw [hn]
  exact hCb Q ρ m N σ J i B S D hD hsep hscale x z k hk

end Falconer

end OAI
