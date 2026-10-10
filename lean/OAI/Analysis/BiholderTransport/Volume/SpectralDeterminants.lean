import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.EndpointSpectrumBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SpectralDeterminants
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_eq_prod_singularValues (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    expJacobian x p = ∏ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i := by
  change (endpointExpDifferential x p).toLinearMap.normDet=_
  rw [LinearMap.normDet_eq_prod_singularValues,Fin.prod_univ_eq_prod_range]
  rfl

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_comparison_of_singularValues {x : M}
    {p q : TangentSpace 𝓘(ℝ,Model n) x} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*(endpointExpDifferential x p).toLinearMap.singularValues i ≤
        (endpointExpDifferential x q).toLinearMap.singularValues i) :
    c^Module.finrank ℝ (Model n)*expJacobian x p ≤ expJacobian x q := by
  rw [expJacobian_eq_prod_singularValues,expJacobian_eq_prod_singularValues]
  have HH := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (Model n)))))
    (fun i _ => mul_nonneg hc ((endpointExpDifferential x p).toLinearMap.singularValues_nonneg i))
    (fun i _ => h i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using HH

lemma uniform_radial_expJacobian_comparison :
    ∃ c : ℝ, 0<c ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ θ∈Icc (1/2:ℝ) 1,
      c*expJacobian x p ≤ expJacobian x (θ • p) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  refine ⟨a^Module.finrank ℝ (Model n),pow_pos ha _,?_⟩
  intro x p hp θ ht
  apply expJacobian_comparison_of_singularValues ha.le
  intro i
  have HH := (H x p hp (1-θ) (by constructor <;> linarith [ht.1,ht.2]) i).1
  rw [show (1:ℝ)-(1-θ)=θ by ring] at HH
  have hm := mul_nonneg ha.le (show 0 ≤ 1-θ by linarith [ht.2])
  nlinarith only [HH,hm]

lemma WeakMTW.uniform_extended_expJacobian_comparison
    (hmtw : WeakMTW (n := n) (M := M)) {a B : ℝ} (ha : 0<a) (hB : 0<B) :
    ∃ c : ℝ, 0<c ∧ ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q ≤ B →
      (∀ t∈Icc (-a) 1,p+t • q∈minimizingVectors x) →
      c*expJacobian x (p+q) ≤ expJacobian x p := by
  obtain ⟨c,hc,H⟩ := hmtw.uniform_extended_spectral_comparison ha hB
  exact ⟨c^Module.finrank ℝ (Model n),pow_pos hc _,fun x p q hpq hB hline =>
    expJacobian_comparison_of_singularValues hc.le (H x p q hpq hB hline)⟩
end SpectralDeterminants
end WeakMTWTransport

end

end

end

end OAI
