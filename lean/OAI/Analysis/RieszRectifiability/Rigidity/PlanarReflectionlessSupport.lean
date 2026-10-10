import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.IsometricRieszPairing
import OAI.Analysis.RieszRectifiability.Rigidity.ReflectionlessFullSupport
import OAI.Analysis.RieszRectifiability.Flatness.PlaneTestExtensions

namespace OAI

/-!
# Reflectionless measures supported on a plane

Compactly supported plane tests extend to ambient tests, allowing the isometric
pullback of a plane-supported measure to inherit reflectionlessness. Upper and lower
growth bounds then give full support in the intrinsic coordinates. Recovering the
ambient measure identifies its support with the entire isometric plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem planarPullbackMeasure_reflectionless {p d : ℕ}
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d))
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G ν) (a : Ambient (p + 1))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
    ScalarReflectionlessAt (p + 1) (planarPullbackMeasure L ν) a := by
  let μ := planarPullbackMeasure L ν
  have hgμ : GlobalUpperGrowth (p + 1) G μ := planarPullbackMeasure_growth L ν hs G hg
  let := hgμ.finite_on_compacts
  have hrec : μ.map L = ν := planarPullbackMeasure_recover L ν hs
  intro e φ K H R hφ hH hR hHR hsφ hmean
  have hc : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hsφ x hn)
  let B : ℝ≥0 := Real.toNNReal ((K : ℝ) * H + |φ a|)
  have hB : ∀ x, |φ x| ≤ (B : ℝ) := by
    intro x
    by_cases hx : φ x = 0
    · rw [hx, abs_zero]
      exact B.coe_nonneg
    have hd : |φ x - φ a| ≤ (K : ℝ) * H := by
      have h := hφ.dist_le_mul x a
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hsφ x hx) K.coe_nonneg)
    have ht := abs_add_le (φ x - φ a) (φ a)
    rw [sub_add_cancel] at ht
    exact (ht.trans (add_le_add hd le_rfl)).trans (Real.le_coe_toNNReal _)
  obtain ⟨ψ, Kψ, hcψ, hψ, _hBψ, hext, _hIvolume, _hmeanvolume⟩ :=
    exists_compact_ambient_plane_test (0 : Ambient d) L φ hc K B hφ hB
  simp only [zero_add] at hext
  have hmeanψ : (∫ x, ψ x ∂ν) = 0 := by
    rw [← hrec, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
    exact (integral_congr_ae (Eventually.of_forall hext)).trans hmean
  obtain ⟨J, hJ, hJs⟩ := hcψ.isBounded.subset_closedBall_lt 0 (L a)
  have hsψ : ∀ x, ψ x ≠ 0 → dist x (L a) ≤ J := by
    intro x hx
    exact hJs (subset_tsupport ψ hx)
  let S := max (2 * J) (2 * H) + 1
  have hS : 0 < S := by
    have h := le_max_left (2 * J) (2 * H)
    dsimp only [S]
    linarith
  have hJS : 2 * J ≤ S := by dsimp only [S]; linarith [le_max_left (2 * J) (2 * H)]
  have hHS : 2 * H ≤ S := by dsimp only [S]; linarith [le_max_right (2 * J) (2 * H)]
  have hz := hreflect (L e) ψ Kψ J S hψ hJ.le hS hJS hsψ hmeanψ
  have hpair : rieszScalarPairing (p + 1) ν (L a) S (L e) ψ =
      rieszScalarPairing (p + 1) μ a S e φ := by
    rw [← hrec, rieszScalarPairing_linearIsometry]
    congr 1
    exact funext hext
  have hlocal := rieszScalarPairing_localization_independent p G μ hgμ e φ K hφ
    a a H H R S hH hH hR hS hHR hHS hsφ hsφ hmean
  exact hlocal.trans (hpair.symm.trans hz)

theorem planar_full_support_of_reflectionless {p d : ℕ}
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d)) (hne : ν ≠ 0)
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ ν (ball x r))
    (hreflect : ∀ a ∈ ν.support, ScalarReflectionlessAt (p + 1) ν a) :
    (planarPullbackMeasure L ν).support = univ ∧
      ν.support = (L.toLinearMap.range : Set (Ambient d)) := by
  have hgμ := planarPullbackMeasure_growth L ν hs G hg
  let := hgμ.finite_on_compacts
  have hfull : (planarPullbackMeasure L ν).support = univ :=
    intrinsic_full_support_of_reflectionless p (planarPullbackMeasure L ν)
      (planarPullbackMeasure_ne_zero L ν hs hne) C G hC hgμ
      (planarPullbackMeasure_lower L ν hs C hlower)
      (fun a ha => planarPullbackMeasure_reflectionless L ν hs G hg a
        (hreflect (L a) ((planarPullbackMeasure_support_iff L ν hs a).mp ha)))
  refine ⟨hfull, Set.Subset.antisymm hs ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hx
  change L y = x at hy
  rw [← hy]
  apply (planarPullbackMeasure_support_iff L ν hs y).mp
  rw [hfull]
  exact mem_univ y

end

end RieszRectifiability

end OAI
