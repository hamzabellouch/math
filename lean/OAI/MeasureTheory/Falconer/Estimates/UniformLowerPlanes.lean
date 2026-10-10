import OAI.MeasureTheory.Falconer.Radial.AffineSubspaceFrostman

namespace OAI

/-! # Uniform lower-plane concentration, with arbitrary affine offset -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

theorem affine_subspace_change_anchor (V : Submodule ℝ (Space d))
    {a p x : Space d} {r : ℝ}
    (hp : p ∈ affineSubspaceNeighborhood V a r)
    (hx : x ∈ affineSubspaceNeighborhood V a r) :
    x ∈ affineSubspaceNeighborhood V p (2*r) := by
  have he : Vᗮ.starProjection (x-p) =
      Vᗮ.starProjection (x-a)-Vᗮ.starProjection (p-a) := by
    rw [← map_sub]
    congr 1
    abel
  change ‖Vᗮ.starProjection (x-p)‖ ≤ _
  change ‖Vᗮ.starProjection (x-a)‖ ≤ r at hx
  change ‖Vᗮ.starProjection (p-a)‖ ≤ r at hp
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [hx,hp])

theorem uniform_lower_plane_frostman (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {M s C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hs : 0 ≤ s-(k:ℝ))
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C) :
    ∃ D : ℝ, 0 < D ∧ ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ k →
      ∀ a : Space d, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ (affineSubspaceNeighborhood V a r) ≤ ENNReal.ofReal (D*r^(s-(k:ℝ))) := by
  let A := max 1 (C*(3:ℝ)^s*(4*M+3)^k)
  have hA : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨A*2^(s-(k:ℝ)),by positivity,?_⟩
  intro V hV a r hr _hr1
  by_cases hsmall : 2*r ≤ 1
  · let T := {p : Space d | ‖p‖ ≤ M ∧ p ∈ affineSubspaceNeighborhood V a r}
    by_cases hT : T.Nonempty
    · obtain ⟨p,hp⟩ := hT
      have hmono : affineSubspaceNeighborhood V a r ⊆ affineSubspaceNeighborhood V p (2*r) :=
        fun _ hx => affine_subspace_change_anchor V hp.2 hx
      apply (measure_mono hmono).trans
      apply (affine_subspace_frostman_bound μ V p hM hp.1 hC hbounded hfrost hV
        (by positivity) hsmall).trans
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
      have hcA : C*(3:ℝ)^s*(4*M+3)^k ≤ A := le_max_right _ _
      have hm : (C*(3:ℝ)^s*(4*M+3)^k)*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) ≤
          A*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcA (by positivity)
      simpa only [mul_assoc] using hm
    · have hzero : μ (affineSubspaceNeighborhood V a r) ≤ μ (∅ : Set (Space d)) := by
        apply measure_mono_ae
        filter_upwards [hbounded] with x hx hnear
        exact (hT ⟨x,hx,hnear⟩).elim
      exact hzero.trans (by rw [measure_empty]; exact bot_le)
  · apply prob_le_one.trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hrp : 1 ≤ (2*r)^(s-(k:ℝ)) := Real.one_le_rpow (by linarith only [hsmall]) hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le] at hrp
    have hm : 1*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) ≤
        A*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    simp only [one_mul] at hm
    simpa only [mul_assoc] using hrp.trans hm

end Falconer

end OAI
