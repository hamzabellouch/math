import OAI.Analysis.CircleDomains.Topology.QuotientOrderedCollar

namespace OAI

/-! Positive collar slices lie inside the punctured coordinate disk. The outer
boundary is used only as a limit, so it need not lie in the open coordinate domain. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem orientedParameter_surjective (a : ℝ) (reverse : Bool) :
    Surjective (orientedParameter a reverse) := by
  intro t
  cases reverse
  · exact ⟨t - a, by dsimp [orientedParameter]; ring⟩
  · exact ⟨1 + a - t, by dsimp [orientedParameter]; ring⟩

 theorem OrderedCollarLift.inner_frontier_punctured
    {H J : ℂ ≃ₜ ℂ} {L : RegularJordanInwardCollar H}
    {π : Sphere → Sphere} (hπ : Continuous π) {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift L (F.comp ⟨π, hπ⟩)) {b : Sphere} (hb : F b = 0)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    {ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ < D.width) :
    ∀ z ∈ frontier (jordanInterior (L.disk ρ)),
      π (z : Sphere) ∈ (((↑) : ℂ → Sphere) '' jordanInterior J) \ {b} := by
  intro z hz
  have hρL : ρ ∈ Icc (0 : ℝ) L.width := ⟨hρ.le, hρw.le.trans D.width_le⟩
  refine ⟨?_, ?_⟩
  · rw [← hregion]
    exact ⟨(z : Sphere), ⟨z, L.inward ρ ⟨hρ, hρL.2⟩ (frontier_subset_closure hz), rfl⟩, rfl⟩
  · obtain ⟨s, _, hzs⟩ := (L.parametrization ρ hρL).boundary.symm ▸ hz
    obtain ⟨t, hts⟩ := orientedParameter_surjective D.start D.reverse s
    have hp := D.projects (ρ, t) ⟨⟨by linarith, hρw⟩, mem_univ _⟩
    change diskRayProjection (D.lift (ρ, t)).val =
      F (π (L.curve |ρ| (orientedParameter D.start D.reverse t) : Sphere)) at hp
    rw [abs_of_pos hρ, hts, hzs] at hp
    intro heq
    rw [mem_singleton_iff.mp heq, hb] at hp
    have hn := congrArg norm hp
    rw [diskRayProjection_norm, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn

end CircleDomainRigidity

end

end OAI
