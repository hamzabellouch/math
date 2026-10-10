import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactForcedLimit
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace OAI

/-! Divided differences of normalized pencil eigenvectors produce an actual
first chain in the compact limit. -/

open Set Filter Topology
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_variable_forced_limit (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (v : ℕ → E) (M : ℝ) (hM : ∀ n, ‖v n‖ ≤ M) (f : E)
    (hf : Tendsto (fun n => v n - K n (v n)) atTop (𝓝 f)) :
    ∃ v₀ : E, v₀ - K₀ v₀ = f ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := by
  have hsmall : Tendsto (fun n => (K n - K₀) (v n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => ‖K n - K₀‖ * M)
    · intro n
      exact ((K n - K₀).le_opNorm (v n)).trans
        (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))
    · have hn : Tendsto (fun n => ‖K n - K₀‖) atTop (𝓝 0) := by
        simpa only [sub_self, norm_zero] using (hK.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => K₀) atTop (𝓝 K₀))).norm
      simpa only [zero_mul] using hn.mul_const M
  apply compact_forced_limit K₀ hc v M hM f
  have hh := hf.add hsmall
  convert hh using 1
  · funext n
    simp only [sub_apply]
    abel
  · simp only [add_zero]

theorem compact_complement_forced_limit (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (L : E →L[ℂ] ℂ) (c : ℝ) (hpos : 0 < c)
    (hbase : ∀ u : E, L u = 0 → c * ‖u‖ ≤ ‖u - K₀ u‖)
    (hclose : ∀ n, ‖K n - K₀‖ ≤ c / 2)
    (v : ℕ → E) (hL : ∀ n, L (v n) = 0) (f : E)
    (hf : Tendsto (fun n => v n - K n (v n)) atTop (𝓝 f)) :
    ∃ v₀ : E, L v₀ = 0 ∧ v₀ - K₀ v₀ = f := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hf).exists_norm_le
  have hv (n : ℕ) : ‖v n‖ ≤ M / (c / 2) := by
    apply (le_div_iff₀ (half_pos hpos)).mpr
    calc
      ‖v n‖ * (c / 2) = c / 2 * ‖v n‖ := mul_comm _ _
      _ ≤ ‖v n - K n (v n)‖ :=
        kernel_complement_perturbation_estimate K₀ (K n) L c hbase (hclose n) (v n) (hL n)
      _ ≤ M := hM _ (mem_range_self n)
  obtain ⟨v₀, he, φ, _hφ, ht⟩ := compact_variable_forced_limit K K₀ hK hc v _ hv f hf
  refine ⟨v₀, ?_, he⟩
  apply tendsto_nhds_unique (L.continuous.continuousAt.tendsto.comp ht)
  change Tendsto (fun n => L (v (φ n))) atTop (𝓝 (0 : ℂ))
  simpa only [hL] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem pencil_divided_difference_equation (K J : E →L[ℂ] E)
    (u v : E) (δ : ℂ) (hu : K u = u) (hv : J v = v) :
    δ⁻¹ • (u - v) - K (δ⁻¹ • (u - v)) = (δ⁻¹ • (K - J)) v := by
  simp only [map_smul, map_sub, hu, smul_apply,
    sub_apply, hv, smul_sub]
  abel

theorem compact_pencil_no_splitting
    (K J D : ℕ → E →L[ℂ] E) (K₀ D₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (hD : Tendsto D atTop (𝓝 D₀)) (L : E →L[ℂ] ℂ)
    (c : ℝ) (hpos : 0 < c)
    (hbase : ∀ u : E, L u = 0 → c * ‖u‖ ≤ ‖u - K₀ u‖)
    (hclose : ∀ n, ‖K n - K₀‖ ≤ c / 2)
    (u v : ℕ → E) (v₀ : E) (hvlim : Tendsto v atTop (𝓝 v₀))
    (hu : ∀ n, K n (u n) = u n) (hv : ∀ n, J n (v n) = v n)
    (hL : ∀ n, L (u n) = L (v n))
    (δ : ℕ → ℂ) (hDdef : ∀ n, D n = (δ n)⁻¹ • (K n - J n))
    (hno : ∀ w : E, w - K₀ w ≠ D₀ v₀) : False := by
  let w := fun n => (δ n)⁻¹ • (u n - v n)
  have hLw (n : ℕ) : L (w n) = 0 := by
    simp only [w, map_smul, map_sub, hL n, sub_self, smul_zero]
  have hw (n : ℕ) : w n - K n (w n) = D n (v n) := by
    rw [hDdef]
    exact pencil_divided_difference_equation (K n) (J n) (u n) (v n) (δ n) (hu n) (hv n)
  have hf : Tendsto (fun n => w n - K n (w n)) atTop (𝓝 (D₀ v₀)) := by
    simp only [hw]
    exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := E) (F := E)).continuous.continuousAt.tendsto.comp
      (hD.prodMk_nhds hvlim)
  obtain ⟨w₀, _, he⟩ := compact_complement_forced_limit K K₀ hK hc L c hpos hbase
    hclose w hLw (D₀ v₀) hf
  exact hno w₀ he

end DefocusingNLS

end OAI
