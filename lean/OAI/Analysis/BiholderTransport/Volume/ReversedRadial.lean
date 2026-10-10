import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.ReverseSpectrum

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ReversedRadial
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_reversed_radial_expJacobian_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ z : TangentBundle 𝓘(ℝ,Model n) M, z.2∈minimizingVectors z.1 →
        ∀ l∈Icc (1/2:ℝ) 1,
        l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
        c*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ≤
          C*expJacobian z.1 z.2) ∧
      (∀ z : TangentBundle 𝓘(ℝ,Model n) M, z.2∈minimizingVectors z.1 →
        ∀ l∈Icc (1:ℝ) 2,
        c*expJacobian z.1 z.2 ≤
          C*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)) := by
  obtain ⟨c,hc,Hc⟩ := uniform_radial_expJacobian_comparison (n := n) (M := M)
  obtain ⟨C,hC,HC⟩ := uniform_reverse_expJacobian_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_,?_⟩
  · intro z hz l hl hr
    have hl0 : l≠0 := ne_of_gt (by linarith [hl.1])
    have H := Hc (reverseRay z).1 (l⁻¹ • (reverseRay z).2) hr l hl
    rw [smul_smul,mul_inv_cancel₀ hl0,one_smul] at H
    exact H.trans (HC z hz)
  · intro z hz l hl
    have hl1 : l⁻¹∈Icc (1/2:ℝ) 1 := by
      constructor
      · exact (le_inv_comm₀ (by norm_num) (by linarith [hl.1])).mpr (by simpa using hl.2)
      · exact inv_le_one_of_one_le₀ hl.1
    have H := Hc (reverseRay z).1 (reverseRay z).2 (reverseRay_minimizing hz) l⁻¹ hl1
    have R := HC (reverseRay z) (reverseRay_minimizing hz)
    rw [reverseRay_reverseRay] at R
    calc c*expJacobian z.1 z.2 ≤ c*(C*expJacobian (reverseRay z).1 (reverseRay z).2) :=
          mul_le_mul_of_nonneg_left R hc.le
      _ = C*(c*expJacobian (reverseRay z).1 (reverseRay z).2) := by ring
      _ ≤ C*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2) :=
          mul_le_mul_of_nonneg_left H hC.le
end ReversedRadial
end WeakMTWTransport

end

end

end

end OAI
