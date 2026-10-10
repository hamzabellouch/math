import OAI.Geometry.RCD.Harmonic.EuclideanRadialGreen
import OAI.Geometry.RCD.Coordinates.FrozenJetTransport

namespace OAI

/-! # Euclidean Laplacians under dilation and translation -/

open Set Metric Filter InnerProductSpace Laplacian
open scoped ContDiff Topology

noncomputable section
namespace RegularPointCoordinates

/-- The Laplacian gains exactly two powers of a scalar input dilation. -/
theorem laplacian_affine_dilation {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (p : Euclidean n) (t : ℝ) (x : Euclidean n) :
    (Δ (fun y => f (p+t • y))) x = t^2*(Δ f) (p+t • x) := by
  let L : Euclidean n →L[ℝ] Euclidean n := t • ContinuousLinearMap.id ℝ _
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin n) ℝ),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ 2 (fun y => f (p+L y)) x _ = _
  rw [iteratedFDeriv_comp_affine_apply L f p x 2 hf.contDiffAt]
  change (iteratedFDeriv ℝ 2 f (p+t • x))
    (fun j : Fin 2 => t • (![EuclideanSpace.single i 1,EuclideanSpace.single i 1] : Fin 2 → Euclidean n) j) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [pow_two]

/-- Classical local harmonicity is preserved by an affine dilation. -/
theorem harmonicOnNhd_affine_dilation {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) {Ω : Set (Euclidean n)}
    (hh : HarmonicOnNhd f Ω) (p : Euclidean n) (t : ℝ) :
    HarmonicOnNhd (fun y => f (p+t • y)) {x | p+t • x ∈ Ω} := by
  have hc : ContDiff ℝ 2 (fun y => f (p+t • y)) :=
    hf.comp (contDiff_const.add (contDiff_id.const_smul t))
  intro x hx
  refine ⟨hc.contDiffAt,?_⟩
  have he := (hh (p+t • x) hx).2.comp_tendsto
    ((continuous_const.add (continuous_const_smul t)).tendsto x)
  filter_upwards [he] with y hy
  change (Δ f) (p+t • y) = 0 at hy
  rw [laplacian_affine_dilation hf,hy]
  simp only [Pi.zero_apply,mul_zero]

end RegularPointCoordinates

end

end OAI
