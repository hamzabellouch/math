import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_one_on_compact {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) ∧ tsupport φ ⊆ U ∧ ∀ x ∈ K, φ x = 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hbone,hbzero,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hbs : tsupport b ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro y hy
    by_contra hn
    exact hy (hbzero y hn)
  have hbc : HasCompactSupport (b : E → ℝ) := hL.of_isClosed_subset (isClosed_tsupport b) hbs
  exact ⟨hbc.toSchwartzMap b.contMDiff.contDiff,hbc,hbs.trans hLU,hbone.self_of_nhdsSet⟩
end TamingCompatibility.SchwartzCutoff

namespace TamingCompatibility.HilbertSobolev
open Set TemperedDistribution
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma tests_eq_of_localize {U : Set E} (hU : IsOpen U) {u v : 𝓢'(E,F)}
    (h : ∀ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) → tsupport χ ⊆ U →
      smulLeftCLM F χ u = smulLeftCLM F χ v)
    (φ : 𝓢(E,ℂ)) (hc : HasCompactSupport (φ : E → ℂ)) (hφU : tsupport φ ⊆ U) :
    u φ = v φ := by
  obtain ⟨χ,hχ,hχU,hχone⟩ := SchwartzCutoff.exists_one_on_compact hc hU hφU
  let ψ : 𝓢(E,ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM χ
  have hs : tsupport ψ ⊆ tsupport χ := tsupport_comp_subset (map_zero Complex.ofRealCLM) χ
  have he := congrArg (fun w : 𝓢'(E,F) => w φ) (h ψ
    (hχ.of_isClosed_subset (isClosed_tsupport ψ) hs) (hs.trans hχU))
  have hp : SchwartzMap.smulLeftCLM ℂ ψ φ = φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]
    by_cases hx : x ∈ tsupport φ
    · change (χ x : ℂ) * φ x = φ x
      rw [hχone x hx,Complex.ofReal_one,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,smul_zero]
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = v (SchwartzMap.smulLeftCLM ℂ ψ φ) at he
  rwa [hp] at he
end TamingCompatibility.HilbertSobolev

end

end OAI
