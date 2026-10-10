import OAI.Geometry.RCD.Coordinates.OpenRegularCutoff

namespace OAI

/-! # Compact interior support implies zero-boundary Sobolev membership -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.sobolev_mem_dirichlet_of_compact_support {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {Ω S : Set X} (hΩ : IsOpen Ω) (hS : IsCompact S) (hs : S ⊆ Ω)
    (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ᵐ x ∂hausdorff n X, x ∉ S →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic u x=0) :
    u ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω := by
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨χ,hχ,hχ1⟩ := hX.exists_open_regular_cutoff hn hΩ hS hs
  let M := SobolevSpace.cutoffCLM μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1)
  have heq : M u = u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) u,hu] with x hx hu
    change SobolevSpace.toLp μ hX.quadratic (M u) x = SobolevSpace.toLp μ hX.quadratic u x
    rw [hx]
    by_cases hs : x ∈ S
    · rw [hχ1 x hs,one_mul]
    · rw [hu hs,mul_zero]
  rw [← heq]
  exact SobolevSpace.cutoffCLM_mem_dirichlet μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1) hχ u

theorem NoncollapsedRCD.gamma_representative_mem_dirichlet {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {Ω : Set X} (hΩ : IsOpen Ω)
    (f g G : SobolevSpace (hausdorff n X) hX.quadratic)
    {φ : X → ℝ} (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (hg : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] φ)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic f g) :
    G ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω := by
  let μ := hausdorff n X
  apply hX.sobolev_mem_dirichlet_of_compact_support hn hΩ hc hs G
  filter_upwards [hg,hG,localGamma_zero_on_level μ hX.quadratic g f 0,
    localGamma_comm μ hX.quadratic f g] with x hx hGx hz hcomm hxs
  rw [hGx,hcomm]
  apply hz
  exact hx.trans (image_eq_zero_of_notMem_tsupport hxs)

end RegularPointCoordinates

end

end OAI
