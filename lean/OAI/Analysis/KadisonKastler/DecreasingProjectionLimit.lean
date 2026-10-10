import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Strong limits of decreasing closed-subspace projections

Applied to the commutation subspaces and remaining corners of a chain
of orthogonal projection families.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem decreasing_closed_projection_tendsto {ι : Type*} [Preorder ι]
    (K : ι → ClosedSubmodule ℂ H) (hK : Antitone K) (x : H) :
    Tendsto (fun i => (K i).toSubmodule.starProjection x) atTop
      (𝓝 ((⨅ i, K i).toSubmodule.starProjection x)) := by
  let U (i : ι) : Submodule ℂ H := (K i)ᗮ.toSubmodule
  have hU : Monotone U := fun _ _ hij => ClosedSubmodule.orthogonal_le (hK hij)
  have hs : (⨆ i, U i).topologicalClosure=(⨆ i, (K i)ᗮ).toSubmodule := by
    exact (ClosedSubmodule.toSubmodule_iSup (fun i => (K i)ᗮ)).symm
  have hoo (L : ClosedSubmodule ℂ H) : Lᗮᗮ=L := by
    ext z
    change z ∈ L.toSubmoduleᗮᗮ ↔ z ∈ L.toSubmodule
    rw [Submodule.orthogonal_orthogonal]
  have hi : (⨆ i, (K i)ᗮ)=(⨅ i, K i)ᗮ := by
    have hh := congrArg ClosedSubmodule.orthogonal
      (ClosedSubmodule.iInf_orthogonal (fun i => (K i)ᗮ))
    simpa only [hoo] using hh.symm
  have ht := Submodule.starProjection_tendsto_closure_iSup U hU x
  have hs' : (⨆ i, U i).topologicalClosure=((⨅ i, K i)ᗮ).toSubmodule := hs.trans (congrArg _ hi)
  have hp : (⨆ i, U i).topologicalClosure.starProjection=
      ((⨅ i, K i)ᗮ).toSubmodule.starProjection := by
    congr 1
  rw [hp] at ht
  have he (L : ClosedSubmodule ℂ H) : Lᗮ.toSubmodule.starProjection x=
      x-L.toSubmodule.starProjection x := by
    change L.toSubmoduleᗮ.starProjection x=x-L.toSubmodule.starProjection x
    rw [Submodule.starProjection_orthogonal]
    rfl
  simp only [U,he] at ht
  have hc : Tendsto (fun _ : ι => x) atTop (𝓝 x) := tendsto_const_nhds
  simpa only [sub_sub_cancel] using hc.sub ht

end

end KadisonKastler

end OAI
