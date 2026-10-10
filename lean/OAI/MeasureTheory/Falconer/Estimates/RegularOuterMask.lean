import OAI.MeasureTheory.Falconer.Estimates.RegularListRestoration
import OAI.MeasureTheory.Falconer.Estimates.GlobalDescriptorBounds

namespace OAI

/-! # The actual outer mask, with both oriented restoration identities -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularOuterMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) : Space d → Space d → ℝ :=
  descriptorAmbientProduct Q ρ (fun u => profile (u/N)) N σ
    (PlanarFalconer.sourceSmoothingLevels σ κ) 0
    (regularOuterList (d := d) profile N κ c) (descriptorNets d N σ)

theorem regularOuterMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) :
    Measurable (Function.uncurry (regularOuterMask Q ρ profile N σ κ c)) :=
  descriptorAmbientProduct_measurable ..

theorem regularOuterMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) (x w : Space d) :
    regularOuterMask Q ρ profile N σ κ c x w ∈ Icc (0:ℝ) 1 := by
  unfold regularOuterMask descriptorAmbientProduct
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
  · exact Finset.prod_le_one₀
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).2)

theorem uniform_regularOuterMask_restoration {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ),
      ∀ c ≤ N, ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (x y : Space d),
      x ∈ Q.carrier → x ≠ y → (x,y) ∈ G →
      (x,y) ∉ allDescriptorTestBad w₀ Q ρ (fun u => profile (u/N)) N σ
        (PlanarFalconer.sourceSmoothingLevels σ κ) G →
      regularOuterMask Q ρ profile N σ κ c x (NormedSpace.normalize (x-y)) = 1 ∧
      regularOuterMask Q ρ profile N σ κ c x (NormedSpace.normalize (y-x)) = 1 := by
  have hJ := PlanarFalconer.sourceSmoothingLevels_pos hσ hκ
  obtain ⟨N₁,h₁⟩ := uniform_all_tests_restoration (d := d) hσ hJ
  obtain ⟨N₂,h₂⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN hNp Q hQ ρ _ profile c hc w₀ G x y hx hxy hG hgood
  have hvalid := regularOuterList_subset_valid (d := d) profile hNp hκ hc
  constructor
  · exact h₁ N ((le_max_left _ _).trans hN) Q hQ ρ _ _ hvalid _
      (fun b _ => descriptorNets_cover d N σ b) w₀ G x y hx hxy hG hgood
  · have hh := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ _ _
      (fun b hb => (mem_validDescriptors N b).mp (hvalid hb)) _
      (fun b _ => descriptorNets_cover d N σ b) 0 x hx (normalizeToSphere w₀ (y-x)) (by
        intro b hb
        by_contra hn
        exact hgood (mem_iUnion₂.mpr ⟨b,hvalid hb,hG,hn⟩))
    rw [← descriptorAmbientProduct_sphere] at hh
    simpa only [regularOuterMask,normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy.symm)] using hh

end Falconer

end OAI
