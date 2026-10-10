import OAI.Analysis.Mahler.PunctureCutoff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- C2 regularity of a form gives C1 regularity of its actual exterior derivative. -/
theorem contDiffAt_extDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E}
    (hω : ContDiffAt ℝ 2 ω x) : ContDiffAt ℝ 1 (extDeriv ω) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ ω) x := hω.fderiv_right (by norm_num)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (n := n)).contDiff.contDiffAt.comp x hd

/-- Smooth separation extends a C2 form near a closed subset of its open
regularity domain, with exact equality on a neighborhood of that subset. -/
theorem exists_closed_set_form_extension {d n : ℕ} {U K : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 2 ω U) :
    ∃ η : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ,
      ContDiff ℝ 2 η ∧ (∀ x ∈ K, η =ᶠ[𝓝 x] ω) := by
  have hdis : Disjoint Uᶜ K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    exact hx (hKU hxK)
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin d → ℝ) hU.isClosed_compl hK hdis (n := 2)
  have hχ : ContDiff ℝ 2 χ := χ.contMDiff.contDiff
  refine ⟨fun x => χ x • ω x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hω.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, χ y = 0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    have ho : ∀ᶠ y in 𝓝 x, χ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [ho] with y hy
    simp [hy]

/-- An exact form integrates to zero over the closed sphere. Its primitive
need only be C2 on an open neighborhood of the sphere, not inside the ball. -/
theorem sphereFlux_extDeriv_eq_zero {n : ℕ} {U : Set (Fin (n+1+1) → ℝ)}
    (r : ℝ) (hU : IsOpen U)
    (hSU : {x | radiusSq x = r^2} ⊆ U)
    (ω : (Fin (n+1+1) → ℝ) → (Fin (n+1+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 2 ω U) : sphereFlux r (extDeriv ω) = 0 := by
  obtain ⟨η, hη, he⟩ := exists_closed_set_form_extension hU
    (isClosed_eq (continuous_radiusSq _) continuous_const) hSU ω hω
  have hde (x) (hx : radiusSq x = r^2) : extDeriv η x = extDeriv ω x := by
    unfold extDeriv
    rw [(he x hx).fderiv_eq]
  rw [← sphereFlux_congr r (extDeriv η) (extDeriv ω) hde]
  have hs := integral_extDeriv_ball_local r (extDeriv η) isOpen_univ
    (contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_extDeriv hη.contDiffAt)).contDiffOn
    (subset_univ _)
  rw [← hs]
  have hd : extDeriv (extDeriv η) = 0 := extDeriv_extDeriv hη (by simp)
  simp [hd]

end MahlerStokes

end

end OAI
