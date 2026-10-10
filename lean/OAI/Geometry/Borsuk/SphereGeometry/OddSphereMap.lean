import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.SphereExtension
import OAI.Geometry.Borsuk.MatrixGeometry.SymmetricCoordinates

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

noncomputable def sphereExtension (f : E → ι → ℝ)
    (x : EuclideanSpace ℝ (UpperTriangle ν)) : EuclideanSpace ℝ ι :=
  normalizedSignedExtension f (symmetricCoordinates x)

lemma Admissible.sphereExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {x : EuclideanSpace ℝ (UpperTriangle ν)} (hx : ‖x‖ = 1) : ‖sphereExtension f x‖ = 1 := by
  apply hf.normalizedSignedExtension_norm (symmetricCoordinates_selfAdjoint x)
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

omit [Nonempty ν] in
lemma sphereExtension_odd (f : E → ι → ℝ) (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    sphereExtension f (-x) = -sphereExtension f x := by
  simp only [sphereExtension, map_neg, normalizedSignedExtension_odd]

lemma Admissible.sphereExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (sphereExtension f) {x : EuclideanSpace ℝ (UpperTriangle ν) | ‖x‖ = 1} := by
  apply hf.normalizedSignedExtension_continuousOn.comp
    (symmetricCoordinates.continuous_of_finiteDimensional.continuousOn) (fun x hx => ?_)
  refine ⟨symmetricCoordinates_selfAdjoint x, ?_⟩
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

end OddSphereMap

end BorsukNine

namespace BorsukNine.SmithTheory

variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

lemma exists_factor_of_ker_le (N : P →ₗ[K] P) (φ : P →ₗ[K] Q)
    (h : LinearMap.ker N ≤ LinearMap.ker φ) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  let ψ₀ : LinearMap.range N →ₗ[K] Q :=
    (N.ker.liftQ φ h).comp N.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := ψ₀.exists_extend
  refine ⟨ψ, ?_⟩
  ext x
  have he := LinearMap.congr_fun hψ ⟨N x, LinearMap.mem_range_self N x⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ψ₀,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] using he

lemma exists_factor_of_vanish_norm (N : P →ₗ[K] P)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : P →ₗ[K] Q)
    (hφ : φ.comp N = 0) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  apply exists_factor_of_ker_le N φ
  intro x hx
  obtain ⟨y, rfl⟩ := hexact hx
  exact LinearMap.congr_fun hφ y

lemma tower_augmentation_zero (d N : P →ₗ[K] P)
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (n : ℕ) (φ : P →ₗ[K] Q) (hφN : φ.comp N = 0) (hφd : φ.comp d = 0)
    (c : ℕ → P) (htower : ∀ i < n, d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) : φ (c 0) = 0 := by
  induction n generalizing φ c with
  | zero =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    rw [← hψ, LinearMap.comp_apply, htop, map_zero]
  | succ n ih =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    have hN : (ψ.comp d).comp N = 0 := by
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hψ, hφd]
    have hd' : (ψ.comp d).comp d = 0 := by
      rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]
    have hh := ih (ψ.comp d) hN hd' (fun i => c (i + 1))
      (fun i hi => htower (i + 1) (Nat.add_lt_add_right hi 1)) htop
    rw [← hψ, LinearMap.comp_apply, ← htower 0 (Nat.zero_lt_succ n)]
    exact hh

end BorsukNine.SmithTheory

end OAI
