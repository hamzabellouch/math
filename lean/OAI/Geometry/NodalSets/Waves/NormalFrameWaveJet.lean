import OAI.Geometry.NodalSets.Charts.NormalFrameContinuous
import OAI.Geometry.NodalSets.Waves.UniformWaveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem normal_frame_smooth_wave_jets_continuous
    (a bb S : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hbb : Continuous bb) (hS : Continuous S)
    (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hbb0 : ∀ t, bb t ≠ 0)
    (hlen : ∀ t, bb t ^ 2 = a t ^ 2 + 4) (hH : ∀ t i j, H t i j = H t j i)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (G : T → Fin 4 → Fin 4 → CPoly) (B : T → Fin 4 → CPoly)
    (hG : ∀ i j, ContinuousPolyFamily (fun t ↦ G t i j))
    (hB : ∀ i, ContinuousPolyFamily (fun t ↦ B t i))
    (hg : ∀ t i j, ContDiff ℝ ∞ (g t i j)) (hb : ∀ t i, ContDiff ℝ ∞ (b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (G t i j) = if i = j then 1 else 0)
    (hmetricFirst : ∀ t i j, homogeneousComponent 1 (G t i j) = 0) (m J : ℕ)
    (hgj : ∀ t i j, FlatAt m (fun x ↦ g t i j x - reval (G t i j) x) 0)
    (hbj : ∀ t i, FlatAt m (fun x ↦ b t i x - reval (B t i) x) 0) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initialPhaseJet (S t) (normalFrameVector (a t) (bb t))
        (normalComplexHessian (a t) (bb t) (H t)) k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0) ∧
      (∀ t, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0) ∧
      ∀ j, j < J → ∀ t, FlatAt m
        (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
          (smoothBeamScalar (g t) (b t) (reval (phi t)))
          (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
          (reval (A (j + 1) t))) 0 := by
  apply smooth_wave_jets_continuous (fun t ↦ normalFrameVector (a t) (bb t))
    (normalFrameVector_continuous a bb ha hbb) 0
    (fun t ↦ by simpa [normalFrameVector] using (Complex.ofReal_ne_zero.mpr (ha0 t)))
    g b G B hG hB hg hb hmetric
    (fun t ↦ initialPhaseJet (S t) (normalFrameVector (a t) (bb t))
      (normalComplexHessian (a t) (bb t) (H t)))
    (fun t k ↦ initialPhaseJet_homogeneous _ _ _ k)
    (normal_frame_initial_jets_continuous a bb S H ha hbb hS hHc ha0 hbb0)
    (fun t i ↦ initialPhaseJet_first _ _ _ i)
    (fun t ↦ normalFrameVector_null (hlen t))
    (fun t ↦ initialPhaseJet_second _ _ _
      (normalComplexHessian_symmetric (ha0 t) (hbb0 t) (H t) (hH t))
      (normalComplexHessian_contract (ha0 t) (hbb0 t) (H t))
      (fun r i j ↦ homogeneousComponent r (G t i j)) (hmetricFirst t)) m J hgj hbj

end
end Yau.Jets

end OAI
