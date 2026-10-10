import OAI.MeasureTheory.Falconer.Radial.TwoSlabGeometry

namespace OAI

/-! # Frostman mass of the intersection of two transversely oriented slabs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem two_slab_frostman_bound (μ : Measure (Space d))
    (u v : Space d) (a b : ℝ) {M s C τ r : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 < r)
    (hsep : τ ≤ normalDistance u v) (hsmall : 10*r/τ ≤ 1) :
    μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*r/τ)^(s-((d-2:ℕ):ℝ))) := by
  let X := {x : Space d | ‖x‖ ≤ M ∧
    |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r}
  have hmono : μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤ μ X := by
    apply measure_mono_ae
    filter_upwards [hbounded] with x hx
    exact fun h => ⟨hx,h⟩
  by_cases hX : X.Nonempty
  · obtain ⟨p,hp⟩ := hX
    obtain ⟨V,hV,hnear⟩ := two_slab_intersection_near_plane u v hu hv hτ hτ1 hr.le hsep
    have hXnear : X ⊆ affineSubspaceNeighborhood V p (10*r/τ) := by
      intro x hx
      exact hnear p x a b hp.2.1 hp.2.2 hx.2.1 hx.2.2
    exact hmono.trans ((measure_mono hXnear).trans
      (affine_subspace_frostman_bound μ V p hM hp.1 hC hbounded hfrost hV.le
        (by positivity) hsmall))
  · rw [Set.not_nonempty_iff_eq_empty.mp hX,measure_empty] at hmono
    exact hmono.trans bot_le

end Falconer

end OAI
