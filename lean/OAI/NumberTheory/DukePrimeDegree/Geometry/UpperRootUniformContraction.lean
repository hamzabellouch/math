import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootContraction

namespace OAI

/-!
# Uniform contraction of bounded upper-root boxes

Strictly contracting root weights shrink every bounded root cube into
any prescribed identity neighborhood, uniformly over the cube. This is
the geometric control used by the unstable conditional entropy argument.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_upperRootCube_iff_size_lt (n : ℕ) {R : ℝ} (hR : 0 < R) (t : UpperRootTime n) :
    t ∈ (completeRootChain n).cube R ↔ upperRootSize n t < R := by
  rw [upperRootEuclideanCoordinates_cube, upperRootSize, pi_norm_lt_iff hR]
  simp only [Real.norm_eq_abs]

theorem upperRootCube_uniform_contraction (n : ℕ) (ell : Fin n → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots n, ε ≤ ell p.val.2 - ell p.val.1)
    (R η : ℝ) (hR : 0 < R) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ t ∈ (completeRootChain n).cube R,
      (completeRootChain n).rootDilation ell r t ∈ (completeRootChain n).cube η := by
  have hlim : Tendsto (fun r : ℝ => Real.exp (-ε * r) * R) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hε tendsto_id)).mul_const R
    simpa only [Function.comp_def, id_eq, neg_mul, zero_mul] using H
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 η hη)
  refine ⟨max 0 r₁, le_max_left _ _, ?_⟩
  intro r hr t ht
  apply (mem_upperRootCube_iff_size_lt n hη _).mpr
  have hsize : upperRootSize n t ≤ R := ((mem_upperRootCube_iff_size_lt n hR t).mp ht).le
  have hb := upperRootSize_dilation_le n ell ε r hgap (le_trans (le_max_left _ _) hr) t
  have hm := mul_le_mul_of_nonneg_left hsize (Real.exp_pos (-ε * r)).le
  exact hb.trans_lt (hm.trans_lt (hr₁ r (le_trans (le_max_right _ _) hr)))

end DukePrimeDegree

end

end OAI
