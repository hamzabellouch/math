import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorChannels
import OAI.Probability.FreeIsing.Trees.CutContinuationChannels
import OAI.Probability.FreeIsing.Trees.PathSideBranches

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.InwardCutChannels

open RootedBroadcast CutContinuationChannels

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def regionProduct
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (theta : ℝ)
    (R : ℕ → Set (TreeVertex d)) (r : ℕ → TreeVertex d) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta
    (Real.artanh (selectedPosterior rho F
      (Subtype.val : R i → TreeVertex d) (r i) z)) ^ 2

theorem exists_regionProduct_channel
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (p : TreeVertex d)
    (R : ℕ → Set (TreeVertex d)) (r : ℕ → TreeVertex d) (s : Finset ℕ)
    (hR : ∀ i, R i ⊆ PathSideBranches.cone p) :
    ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, regionProduct rho F theta R r s z = g (globalCone p z) := by
  have hex (i : ℕ) : ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, responseAttenuation theta
        (Real.artanh (selectedPosterior rho F (Subtype.val : R i → TreeVertex d)
          (r i) z)) ^ 2 = g (globalCone p z) := by
    exact exists_selectedAttenuation_local_channel rho hF
      (Subtype.val : DescendantVertex p → TreeVertex d)
      (fun u : R i => (⟨u.1, hR i u.2⟩ : DescendantVertex p)) (r i) hθ
  choose g hg hb heq using hex
  refine ⟨fun z => ∏ i ∈ s, g i z,
    s.measurable_fun_prod (fun i _ => hg i), ?_, ?_⟩
  · intro z
    exact ⟨Finset.prod_nonneg (fun i _ => (hb i z).1),
      Finset.prod_le_one₀ (fun i _ => (hb i z).1) (fun i _ => (hb i z).2)⟩
  · intro z
    exact Finset.prod_congr rfl (fun i _ => heq i z)

def regionAverage {W : Type*} [Fintype W]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (theta : ℝ)
    (R : W → ℕ → Set (TreeVertex d)) (r : W → ℕ → TreeVertex d)
    (s : W → Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  (∑ w : W, regionProduct rho F theta (R w) (r w) (s w) z) /
    (Fintype.card W : ℝ)

theorem exists_regionAverage_channel {W : Type*} [Fintype W] [Nonempty W]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (p : TreeVertex d)
    (R : W → ℕ → Set (TreeVertex d)) (r : W → ℕ → TreeVertex d)
    (s : W → Finset ℕ) (hR : ∀ w i, R w i ⊆ PathSideBranches.cone p) :
    ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, regionAverage rho F theta R r s z = g (globalCone p z) := by
  choose g hg hb heq using fun w =>
    exists_regionProduct_channel rho hF hθ p (R w) (r w) (s w) (hR w)
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  refine ⟨fun z => (∑ w : W, g w z) / (Fintype.card W : ℝ),
    (Finset.measurable_fun_sum _ (fun w _ => hg w)).div_const _, ?_, ?_⟩
  · intro z
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun w _ => (hb w z).1)) hc.le
    · apply (div_le_iff₀ hc).mpr
      simpa using Finset.sum_le_sum
        (fun w (_ : w ∈ (Finset.univ : Finset W)) => (hb w z).2)
  · intro z
    unfold regionAverage
    congr 1
    exact Finset.sum_congr rfl (fun w _ => heq w z)

theorem integral_regionAverage_le {W : Type*} [Fintype W] [Nonempty W]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (p : TreeVertex d)
    (R : W → ℕ → Set (TreeVertex d)) (r : W → ℕ → TreeVertex d)
    (s : W → Finset ℕ) (hR : ∀ w i, R w i ⊆ PathSideBranches.cone p)
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsProbabilityMeasure P] {m : ℝ}
    (hmean : ∀ w, (∫ z, regionProduct rho F theta (R w) (r w) (s w) z ∂P) ≤ m) :
    (∫ z, regionAverage rho F theta R r s z ∂P) ≤ m := by
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hi (w : W) : Integrable (regionProduct rho F theta (R w) (r w) (s w)) P := by
    obtain ⟨g, hg, hb, heq⟩ :=
      exists_regionProduct_channel rho hF hθ p (R w) (r w) (s w) (hR w)
    have he : regionProduct rho F theta (R w) (r w) (s w) = g ∘ globalCone p :=
      funext heq
    rw [he]
    apply Integrable.of_bound (hg.comp (measurable_globalCone p)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hb _).1]
      exact (hb _).2)
  calc
    _ = (∑ w : W, ∫ z, regionProduct rho F theta (R w) (r w) (s w) z ∂P) /
        (Fintype.card W : ℝ) := by
      unfold regionAverage
      rw [integral_div, integral_finsetSum _ (fun w _ => hi w)]
    _ ≤ (∑ _w : W, m) / (Fintype.card W : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun w _ => hmean w)) hc.le
    _ = m := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ m hc.ne'

end Problem367.InwardCutChannels

end

end OAI
