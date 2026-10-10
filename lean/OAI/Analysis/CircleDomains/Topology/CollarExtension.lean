import OAI.Analysis.CircleDomains.Topology.CutoffStaircase

namespace OAI

/-!
# Smooth extension of the active filling coordinate

A real branch smooth on a collar can be retained on a smaller closed
collar and extended to be constant away from it. In a filling disk all
other branches are constant, so this is the only extension needed there.
-/

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Multiplication by a smooth cutoff which vanishes near the complement
of `U` makes a branch smooth globally. No regularity of the branch is
required outside its original open domain. -/
theorem contDiff_collar_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f χ : E → ℝ} {n : ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hχ : ContDiff ℝ n χ)
    (hzero : ∀ᶠ x in 𝓝ˢ Uᶜ, χ x = 0) (c : ℝ) :
    ContDiff ℝ n (fun x => c + χ x * (f x - c)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact contDiffAt_const.add
      (hχ.contDiffAt.mul ((hf.contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
  · have heq : (fun y => c + χ y * (f y - c)) =ᶠ[𝓝 x] (fun _ => c) := by
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Retain an arbitrary smooth real branch near a closed collar inside
its domain, and make it constant off that domain. -/
theorem exists_smooth_collar_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U A : Set E} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (c : ℝ) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝ˢ A] f ∧ ∀ x ∉ U, F x = c := by
  have hd : Disjoint Uᶜ A := Set.disjoint_left.mpr (fun x hx hxa => hx (hAU hxa))
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hA hd (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => c + χ x * (f x - c), contDiff_collar_cutoff hU hf hχ hzero c, ?_, ?_⟩
  · filter_upwards [hone] with x hx
    simp [hx]
  · intro x hx
    change c + χ x * (f x - c) = c
    rw [hzero.self_of_nhdsSet x hx]
    ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
