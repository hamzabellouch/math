import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledLower
import OAI.Geometry.TamingCompatibility.Charts.InverseCutoff

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma local_all_orders_smooth {U : Set E} {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolevLoc U n u)
    (χ : 𝓢(E,ℂ)) (hc : HasCompactSupport (χ : E → ℂ)) (hχ : tsupport χ ⊆ U) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧
      smulLeftCLM F χ u = EuclideanSobolev.boundedDistribution g := by
  apply EuclideanSobolev.exists_smooth_representative
  intro s
  obtain ⟨n,hn⟩ := exists_nat_gt s
  exact (hu n χ hc hχ).mono (le_of_lt hn)

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma postcomp_real_tsupport (φ : 𝓢(E,ℝ)) :
    tsupport (SchwartzMap.postcompCLM Complex.ofRealCLM φ) ⊆ tsupport φ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  change (φ x : ℂ) = 0
  rw [hx,Complex.ofReal_zero]

lemma smooth_representative_on_cutoff {U V : Set E} {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolevLoc U n u) (ψ : 𝓢(E,ℂ))
    (hψ : HasCompactSupport (ψ : E → ℂ)) (hψU : tsupport ψ ⊆ U)
    (hone : ∀ x ∈ V, ψ x = 1) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧ ∀ χ : 𝓢(E,ℂ),
      HasCompactSupport (χ : E → ℂ) → tsupport χ ⊆ V →
      smulLeftCLM F χ u = smulLeftCLM F χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨g,hg,he⟩ := local_all_orders_smooth (u := u) hu ψ hψ hψU
  refine ⟨g,hg,fun χ _ hχV => ?_⟩
  rw [← he]
  exact (local_cutoff_one ψ χ (fun x hx => hone x (hχV hx)) u).symm

lemma exists_local_smooth_representative {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U)
    {u : 𝓢'(E,F)} (hu : ∀ n : ℕ, MemSobolevLoc U n u) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∃ g : E →ᵇ F,
      ContDiff ℝ ∞ (g : E → F) ∧ ∀ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) →
        tsupport χ ⊆ V → smulLeftCLM F χ u = smulLeftCLM F χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨φ,hφ,hφU,V,hV,hpV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near (E := E) (U := U) (p := p) hU hp
  let ψ : 𝓢(E,ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hψ : HasCompactSupport (ψ : E → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport ψ) (postcomp_real_tsupport φ)
  have hψU : tsupport ψ ⊆ U := (postcomp_real_tsupport φ).trans hφU
  refine ⟨V,hV,hpV,hVU,?_⟩
  apply smooth_representative_on_cutoff hu ψ hψ hψU
  intro x hx
  change (φ x : ℂ) = 1
  rw [hφone x hx,Complex.ofReal_one]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
