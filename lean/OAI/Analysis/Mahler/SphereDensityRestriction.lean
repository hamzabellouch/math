import OAI.Analysis.Mahler.ReferenceSphereIntegral

namespace OAI

open Complex
namespace Mahler

/-- Pointwise adapted tangent frames suffice; no global tangent frame is
chosen or assumed continuous. -/
theorem exists_outward_tangent_frame {k : ℕ} {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) :
    ∃ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) ∧ sphereVolume k (Matrix.vecCons x v) = 1 := by
  obtain ⟨L,hL⟩ := exists_unitary_referencePole hx
  refine ⟨L ∘ poleFrameFin k, ?_, ?_⟩
  · intro i
    rw [← hL]
    exact (unitary_real_inner L _ _).trans
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (poleFrameVector_tangent _))
  · have he : Matrix.vecCons x (L ∘ poleFrameFin k) =
        L ∘ Matrix.vecCons (referencePole k) (poleFrameFin k) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa [Matrix.vecCons] using hL.symm
    rw [he, sphereVolume_unitary, poleFrameFin_volume]

/-- The ambient cofactor formula depends only on the actual tangent
restriction of the boundary form. -/
theorem orientedDensity_congr_on_tangent {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1)
    {B C : ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ}
    (h : ∀ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) → B v = C v) :
    orientedDensity (sphereFrame k) (sphereVolume k) B x =
      orientedDensity (sphereFrame k) (sphereVolume k) C x := by
  obtain ⟨v,hv,hvol⟩ := exists_outward_tangent_frame hx
  have hB := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) B hx v hv
  have hC := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) C hx v hv
  rw [hvol, mul_one] at hB hC
  rw [← hB, ← hC, h v hv]

lemma orientedDensity_zero {k : ℕ} (x : ComplexEuclidean (k+1)) :
    orientedDensity (sphereFrame k) (sphereVolume k) 0 x = 0 := by
  simp [orientedDensity]

end Mahler

end OAI
