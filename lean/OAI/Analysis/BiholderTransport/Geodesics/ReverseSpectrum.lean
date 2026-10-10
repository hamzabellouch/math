import Mathlib
import OAI.Analysis.BiholderTransport.Volume.SpectralDeterminants

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ReverseSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma sprayFlow_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) (t : ℝ) :
    sprayFlow t (reverseRay z)=tangentScale (-1) (sprayFlow (1-t) z) := by
  rw [reverseRay,sprayFlow_scale,←sprayFlow_add]
  congr 2
  ring

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_reverse_half (z : TangentBundle 𝓘(ℝ,Model n) M) :
    HEq (middleHessian (reverseRay z) (1/2) 1) (middleHessian z (1/2) 1) := by
  unfold middleHessian
  rw [sprayFlow_reverseRay]
  rw [show (1:ℝ)-1/2=1/2 by norm_num]
  change HEq
    ((1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((-(1/2:ℝ)) • ((-1:ℝ) • (sprayFlow (1/2) z).2))+
      (1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((1/2:ℝ) • ((-1:ℝ) • (sprayFlow (1/2) z).2)))
    ((1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((-(1/2:ℝ)) • (sprayFlow (1/2) z).2)+
      (1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((1/2:ℝ) • (sprayFlow (1/2) z).2))
  apply heq_of_eq
  simp only [smul_smul]
  norm_num only
  ext v w
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleSingularValue_reverse_half (z : TangentBundle 𝓘(ℝ,Model n) M) (i : ℕ) :
    middleSingularValue (reverseRay z) (1/2) 1 i=middleSingularValue z (1/2) 1 i := by
  have hb : (sprayFlow (1/2:ℝ) (reverseRay z)).1=(sprayFlow (1/2:ℝ) z).1 := by
    rw [sprayFlow_reverseRay]
    norm_num only
    rfl
  exact intrinsicBilinearSingular_heq hb (middleHessian_reverse_half z) i

lemma uniform_reverse_singular_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential (reverseRay z).1 (reverseRay z).2).toLinearMap.singularValues i ≤
        C*(endpointExpDifferential z.1 z.2).toLinearMap.singularValues i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_endpoint_middle_singular_comparison (n := n) (M := M)
  refine ⟨C*c,mul_pos hC hc,?_⟩
  intro z hz i
  have h0 := (H z.1 z.2 hz (1/2) (by constructor <;> norm_num) i).2
  have h1 := (H (reverseRay z).1 (reverseRay z).2 (reverseRay_minimizing hz)
    (1/2) (by constructor <;> norm_num) i).1
  change _ ≤ C*middleSingularValue (reverseRay z) (1/2) 1 i at h1
  change middleSingularValue z (1/2) 1 i ≤ _ at h0
  rw [middleSingularValue_reverse_half] at h1
  exact h1.trans ((mul_le_mul_of_nonneg_left h0 hC.le).trans_eq (mul_assoc _ _ _).symm)

lemma uniform_reverse_expJacobian_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → expJacobian (reverseRay z).1 (reverseRay z).2 ≤
        C*expJacobian z.1 z.2 := by
  obtain ⟨C,hC,H⟩ := uniform_reverse_singular_comparison (n := n) (M := M)
  refine ⟨C ^ Module.finrank ℝ (Model n),pow_pos hC _,?_⟩
  intro z hz
  rw [expJacobian_eq_prod_singularValues,expJacobian_eq_prod_singularValues]
  have HH := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (Model n)))))
    (fun i _ => (endpointExpDifferential (reverseRay z).1 (reverseRay z).2).toLinearMap.singularValues_nonneg i)
    (fun i _ => H z hz i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using HH
end ReverseSpectrum
end WeakMTWTransport

end

end

end

end OAI
