import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.IsometricLocalTransforms

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function

theorem linearIsometry_ball_integral {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (a : Ambient n) (R : ℝ) (F : Ambient d → ℝ) :
    (∫ x in ball (L a) R, F x ∂μ.map L) = ∫ x in ball a R, F (L x) ∂μ := by
  rw [linearIsometry_restrict_ball, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]

theorem linearIsometry_local_weak_L2_pairings {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (a : Ambient n) (R : ℝ) (T : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hv : MemLp v 2 ((μ.map L).restrict (ball (L a) R)))
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ((μ.map L).restrict (ball (L a) R)) →
      Tendsto (fun j => ∫ x in ball (L a) R, T j x * g x ∂μ.map L) atTop
        (𝓝 (∫ x in ball (L a) R, v x * g x ∂μ.map L))) :
    MemLp (fun x => v (L x)) 2 (μ.restrict (ball a R)) ∧
      ∀ g : Ambient n → ℝ, MemLp g 2 (μ.restrict (ball a R)) →
        Tendsto (fun j => ∫ x in ball a R, T j (L x) * g x ∂μ) atTop
          (𝓝 (∫ x in ball a R, v (L x) * g x ∂μ)) := by
  have hmap := linearIsometry_restrict_ball L μ a R
  have hv' : MemLp v 2 ((μ.restrict (ball a R)).map L) := by rwa [← hmap]
  refine ⟨?_, ?_⟩
  · exact L.isometry.isClosedEmbedding.measurableEmbedding.memLp_map_measure_iff.mp hv'
  intro g hg
  let Φ := fun x : Ambient d => g (L.toContinuousLinearMap.adjoint x)
  have hleft (x : Ambient n) : L.toContinuousLinearMap.adjoint (L x) = x :=
    DFunLike.congr_fun L.adjoint_comp_self x
  have hcomp : Φ ∘ L = g := by
    funext x
    simp only [Φ, Function.comp_apply, hleft]
  have hΦ : MemLp Φ 2 ((μ.map L).restrict (ball (L a) R)) := by
    rw [hmap, L.isometry.isClosedEmbedding.measurableEmbedding.memLp_map_measure_iff, hcomp]
    exact hg
  have hpair (F : Ambient d → ℝ) : (∫ x in ball (L a) R, F x * Φ x ∂μ.map L) =
      ∫ x in ball a R, F (L x) * g x ∂μ := by
    rw [linearIsometry_ball_integral]
    simp only [Φ, hleft]
  simpa only [hpair] using! hweak Φ hΦ

theorem local_capped_weak_L2_pairings_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R : ℝ) (ε : ℕ → ℝ) (v : Ambient d → ℝ)
    (hv : MemLp v 2 ((μ.map L).restrict (ball (L a) R)))
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ((μ.map L).restrict (ball (L a) R)) →
      Tendsto (fun j => ∫ x in ball (L a) R,
        scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) (ε j) (fun _ => 1) x * g x
          ∂μ.map L) atTop (𝓝 (∫ x in ball (L a) R, v x * g x ∂μ.map L))) :
    MemLp (fun x => v (L x)) 2 (μ.restrict (ball a R)) ∧
      ∀ g : Ambient n → ℝ, MemLp g 2 (μ.restrict (ball a R)) →
        Tendsto (fun j => ∫ x in ball a R,
          scalarCappedTransform m (μ.restrict (ball a R)) e (ε j) (fun _ => 1) x * g x ∂μ) atTop
          (𝓝 (∫ x in ball a R, v (L x) * g x ∂μ)) := by
  have h := linearIsometry_local_weak_L2_pairings L μ a R
    (fun j => scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) (ε j) (fun _ => 1))
    v hv hweak
  simpa only [scalarCappedTransform_ball_linearIsometry] using! h

theorem local_transform_constancy_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (H R b : ℝ) (v : Ambient d → ℝ)
    (hconstant : ∀ᵐ x ∂μ.map L, x ∈ ball (L a) H →
      v x + scalarFarRieszTransform m (μ.map L) (L e) (L a) R x = b) :
    ∀ᵐ x ∂μ, x ∈ ball a H → v (L x) + scalarFarRieszTransform m μ e a R x = b := by
  have h := ae_of_ae_map L.continuous.measurable.aemeasurable hconstant
  simpa only [mem_ball, L.dist_map, scalarFarRieszTransform_linearIsometry] using! h

end

end RieszRectifiability

end OAI
