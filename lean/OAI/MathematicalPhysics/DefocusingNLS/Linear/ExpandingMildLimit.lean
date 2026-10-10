import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierTestLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDualForcingBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamelDuality
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierTestExt

namespace OAI

/-! # Physical limits of bounded expanding mild solutions are whole-space mild solutions -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingMild_physical_limit (a b k t M U G : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ht : 0 ≤ t)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (f u : ℕ → FourierL2) (r : ℕ → ℝ → FourierL2)
    (hf : ∀ n, ‖f n‖ ≤ M) (hu : ∀ n, ‖u n‖ ≤ U)
    (hr : ∀ n s, s ∈ Icc 0 t → ‖r n s‖ ≤ G)
    (hrc : ∀ n, ContinuousOn (r n) (Icc 0 t))
    (hmild : ∀ n, u n = expandingFreeStep a b k (L n) t ha hk (hL n) ht (f n) +
      expandingDuhamel a b k (L n) ha hk (hL n) t (r n))
    (v₀ v : HomogeneousY a k) (g : ℝ → HomogeneousY a k)
    (hg : StronglyMeasurable g) (hgi : IntegrableOn g (Icc 0 t))
    (hp₀ : ∀ y : E, Tendsto (fun n => expandingPhysicalContinuous a k (L n)
      ha ha1 hk (hL n) (f n) y) atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk v₀ y)))
    (hp : ∀ y : E, Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) t)
      ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) t (hL n) ht)) (u n) y)
      atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk v y)))
    (hpg : ∀ s (hs : s ∈ Icc 0 t) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) hs.1)) (r n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk (g s) y))) :
    v = homogeneousFreeOperator a b k t ha ha1 hk v₀ +
      homogeneousDuhamel a b k ha ha1 hk t g := by
  apply homogeneousFourierPairing_ext a k ha ha1 hk
  intro φ
  let c : ℂ := ((2 * Real.pi) ^ (12 : ℕ))⁻¹
  let D := fun s => homogeneousFourierPairing a k ha ha1 hk
    (homogeneousFreeDualTest a b (t - s) φ) (g s)
  let F := fun n => expandingDualDuhamelIntegrand a b k (L n) t ha ha1 hk (hL n) φ (r n)
  have h₀ := expandingFourierTest_tendsto_of_physical a k M ha ha1 hk L hL f hf v₀ hp₀
    (homogeneousFreeDualTest a b t φ)
  have hv := expandingFourierTest_tendsto_of_physical a k U ha ha1 hk
    (fun n => expandingRadius (L n) t)
    (fun n => (hL n).trans (expandingRadius_ge (L n) t (hL n) ht)) u hu v hp φ
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      Tendsto (fun n => F n s) atTop (𝓝 (c * D s)) := by
    have h := expandingFourierTest_tendsto_of_physical a k G ha ha1 hk
      (fun n => expandingRadius (L n) s)
      (fun n => (hL n).trans (expandingRadius_ge (L n) s (hL n) hs.1))
      (fun n => r n s) (fun n => hr n s hs) (g s) (hpg s hs)
      (homogeneousFreeDualTest a b (t - s) φ)
    simpa only [F, D, c, expandingDualDuhamelIntegrand, dite_eq_left hs] using h
  have hI : Tendsto (fun n => ∫ s in Icc 0 t, F n s) atTop
      (𝓝 (c * ∫ s in Icc 0 t, D s)) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Icc 0 t))
      (fun _ => (expandingEmbeddingBound a k * SchwartzMap.seminorm ℂ 0 0 φ) * G)
      (fun n => (integrableOn_expandingDualDuhamelIntegrand a b k (L n) t
        ha ha1 hk (hL n) ht φ (r n) (hrc n)).aestronglyMeasurable)
      (integrableOn_const isCompact_Icc.measure_ne_top)
      (fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact expandingDualDuhamelIntegrand_bound a b k (L n) t G
          ha ha1 hk (hL n) ht φ (r n) s hs (hr n s hs))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hd s hs)
    simpa only [integral_const_mul] using h
  have hsum := h₀.add hI
  have hsame : Tendsto (fun n => expandingFourierTest a k (expandingRadius (L n) t)
      ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) t (hL n) ht)) φ (u n)) atTop
      (𝓝 (c * homogeneousFourierPairing a k ha ha1 hk
        (homogeneousFreeDualTest a b t φ) v₀ + c * ∫ s in Icc 0 t, D s)) := by
    convert hsum using 1
    funext n
    exact expandingMild_fourier_duality a b k (L n) t ha ha1 hk (hL n) ht φ
      (f n) (u n) (r n) (hrc n) (hmild n)
  have he := tendsto_nhds_unique hv hsame
  rw [map_add, homogeneousFreeOperator_fourier_duality,
    homogeneousDuhamel_fourier_duality a b k t ha ha1 hk ht φ g hg hgi]
  have hc : c ≠ 0 := by
    have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    exact inv_ne_zero (pow_ne_zero _ hp)
  apply mul_left_cancel₀ hc
  simpa only [mul_add, c, D] using he

end DefocusingNLS

end OAI
