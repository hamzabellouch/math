import OAI.MeasureTheory.Falconer.Fourier.SymbolProduct
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower

namespace OAI

/-!
# The actual buffered masks satisfy finite symbol budgets

Derivative constants depend on dimension and the fixed budget, never on
the number of descriptors. Only a polynomial factor in the list size
enters positive-order derivatives, and this is absorbed into R^sigma.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem buffered_mask_product_bound (n K j : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type*} [DecidableEq ι]
      (I : Finset ι) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
      (S : ι → Finset (Sphere (n+2))) (U : ι → Set (Sphere (n+2))) (k : ι → ℕ),
      (∀ i, δ i ≤ 1) →
      (∀ i, ∀ x ∈ S i, ∀ y ∈ S i, x ≠ y → δ i/2 ≤ dist x y) →
      (∀ i, ∀ w : Sphere (n+2), ∃ c ∈ S i, dist w c ≤ δ i/2) →
      (∑ i ∈ I, k i) ≤ K →
      ∀ L : ℝ, 0 ≤ L → (∀ i ∈ I, (δ i)⁻¹ ≤ L) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv j (fun t => ∏ i ∈ I, normalizedChartFactor
        (fun z => capCutoffAmbient (δ i) (hδ i) (S i) (U i) (rotatedChartCurve e y z))
        ((δ i)⁻¹) (k i) t) u‖ ≤ A^(K+j)*((I.card : ℝ)*L)^j := by
  choose B hB hBb using (fun l => capCutoffAmbient_chart_derivatives n l)
  let A := 1+∑ l ∈ Finset.range (K+j+1), B l
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith [Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (K+j+1)) => hB l)]
  have hdom (l : ℕ) (hl : l ≤ K+j) : B l ≤ A := by
    have hh := Finset.single_le_sum (fun z (_ : z ∈ Finset.range (K+j+1)) => hB z)
      (Finset.mem_range.mpr (by omega : l < K+j+1))
    dsimp [A]
    linarith
  refine ⟨A,hA,?_⟩
  intro ι _ I δ hδ S U k hδ1 hsep hcover hbudget L hL hLbound e y hy u hu
  apply normalized_chart_product_bound I _ (fun i => (δ i)⁻¹) k hA hL K j hbudget
    (fun i _ => inv_pos.mpr (hδ i)) hLbound (fun i _ =>
      (capCutoffAmbient_contDiff (hδ i) (S i) (U i)).comp (rotatedChartCurve_contDiff e y)) u
  intro i _hi l hl
  by_cases hz : l = 0
  · subst l
    let w : Sphere (n+2) := sphereMap e (gnomonicChart (coordinateJoin y u))
    have hw := (capCutoffAmbient_properties (hδ i) (S i) (hcover i) (U i)).1 w
    simp only [iteratedDeriv_zero,Function.comp_apply,pow_zero,one_mul,Real.norm_eq_abs]
    change |capCutoffAmbient (δ i) (hδ i) (S i) (U i) (w : Space (n+2))| ≤ 1
    rw [abs_of_nonneg hw.1]
    exact hw.2
  · have hh := hBb l (δ i) (hδ i) (hδ1 i) (S i) (hsep i) (hcover i) (U i) e y hy u hu
    rw [Real.norm_eq_abs]
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr (hδ i).le) l)
    exact (hdom l hl).trans (le_self_pow₀ hA hz)

/-- The list-size loss in the previous theorem is bounded by R^sigma,
with no dependence on the angular or spatial data. -/
theorem descriptor_count_subpower (C : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type*} (I : Finset ι),
      I.card ≤ (N+1)^C → (I.card : ℝ) ≤ ((2 : ℝ)^N)^σ := by
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_polynomial_subpower C hσ
  refine ⟨N₀,?_⟩
  intro N hN ι I hI
  have hh : (I.card : ℝ) ≤ ((N : ℝ)+1)^C := by exact_mod_cast hI
  apply hh.trans
  exact (pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ)+1)
    (by linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N] : (N : ℝ)+1 ≤ 4*(N : ℝ)+1) C).trans (hN₀ N hN)

end Falconer

end OAI
