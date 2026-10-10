import OAI.MeasureTheory.Falconer.Estimates.SmoothCompositionScale

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def frechetCompositionCost (g : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖

theorem frechetCompositionCost_nonneg (g : E → ℝ) (n : ℕ) (x : E) :
    0 ≤ frechetCompositionCost g n x := by
  unfold frechetCompositionCost
  positivity

theorem frechetCompositionCost_continuousAt {g : E → ℝ} {x : E}
    (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ContinuousAt (frechetCompositionCost g n) x := by
  apply tendsto_finsetSum
  intro c _
  apply tendsto_finsetProd
  intro j _
  exact (hg.continuousAt_iteratedFDeriv
    (by exact_mod_cast (le_top : (c.partSize j : ℕ∞) ≤ ⊤))).norm

theorem frechet_composition_scale {f : ℝ → ℂ} {g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ frechetCompositionCost g n x * (C*D^n) := by
  rw [iteratedFDeriv_comp hf hg
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp only [FormalMultilinearSeries.taylorComp, frechetCompositionCost, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
  change ‖iteratedFDeriv ℝ c.length f (g x)‖ *
    (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖) ≤ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  exact (hb c.length c.length_le).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD c.length_le) hC)

theorem compact_frechet_composition_scale {g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (fun x hx => (frechetCompositionCost_continuousAt (hg x hx) n).continuousWithinAt)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hA : frechetCompositionCost g n x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  calc
    _ ≤ frechetCompositionCost g n x * (C*D^n) :=
      frechet_composition_scale hf.contDiffAt (hg x hx) hC hD n (fun k hk => hb k hk _)
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
