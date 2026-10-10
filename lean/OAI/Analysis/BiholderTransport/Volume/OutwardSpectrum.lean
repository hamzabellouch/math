import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.DoubleMountain
import OAI.Analysis.BiholderTransport.Volume.SpectralDeterminants
import OAI.Analysis.BiholderTransport.Convexity.ConvexBarycentricSegment
import OAI.Analysis.BiholderTransport.Coordinates.FiberNormal

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section OutwardSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance outwardSpectrumFiniteDimensionalTangentSpace (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.uniform_outward_expJacobian_comparison
    (hmtw : WeakMTW (n := n) (M := M)) {μ κ L : ℝ}
    (hμ : 0<μ) (hκ : 0<κ) (hL : 0<L) :
    ∃ c : ℝ, 0<c ∧ ∀ (ι : Type) [Fintype ι] (x : M)
      (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
      (p : TangentSpace 𝓘(ℝ,Model n) x),
      (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
      p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
      μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
      κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ L*D → v i=p+t • e →
      c*expJacobian x (v i) ≤ expJacobian x p := by
  obtain ⟨c,hc,H⟩ := hmtw.uniform_extended_expJacobian_comparison hμ
    (div_pos hL (show 0<2*κ by positivity))
  refine ⟨c,hc,?_⟩
  intro ι _ x v w p hw hs hv hp i e t D hi he ht _hD hh hhD hgap hvi
  have hratio := outward_inner_ratio he ht hh hκ hL hhD (hvi ▸ hgap)
  have hline (s : ℝ) (hst : s∈Icc (-μ) 1) : p+s • (t • e)∈minimizingVectors x := by
    have HH := convex_barycentric_segment (hmtw.convex_minimizingVectors x)
      w v hw hs hv i hμ.le hi s hst
    rw [←hp,hvi] at HH
    simpa only [add_sub_cancel_left] using HH
  have HH := H x p (t • e) hratio.1 hratio.2 hline
  rwa [←hvi] at HH
end OutwardSpectrum
end WeakMTWTransport

end

end

end

end OAI
