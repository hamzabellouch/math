import Mathlib
import OAI.Analysis.Commutator.NormalGNS
import OAI.Analysis.Commutator.NormalizedTrace
import OAI.Analysis.Commutator.OrbitFixedTrace
import OAI.Analysis.Commutator.ProjectionNormalBridge

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfac hd hfin

lemma hull_projectionContinuousAtOne (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    PositiveWOT.ProjectionContinuousAtOne M (positive M x f hf) := by
  intro P hP hmono hlim
  exact hull_projection_tendsto M hfac hd hfin x hf 1 (IsStarProjection.one _) P hP hmono
    (fun n => (hP n).le_one) hlim

theorem hull_norm_separable (x : H) :
    TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x) := by
  apply (NormalPredual.finiteTests_separable M (TopologicalSpace.denseSeq H)).closure.mono
  rintro _ ⟨f,hf,rfl⟩
  exact PositiveWOT.mem_predual M (positive M x f hf)
    (hull_projectionContinuousAtOne M hfac hd hfin x hf)

theorem hull_normal (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    NormalGNS.BoundedWOTContinuous M (positive M x f hf) :=
  PositiveWOT.boundedWOTContinuous M (positive M x f hf)
    (hull_projectionContinuousAtOne M hfac hd hfin x hf)

theorem exists_faithful_normal_trace :
    ∃ τ : M →ₚ[ℂ] ℂ,(∀ a b : M,τ (a*b)=τ (b*a)) ∧
      NormalGNS.BoundedWOTContinuous M τ ∧ (∀ a : M,τ (star a*a)=0 → a=0) ∧ τ 1=1 := by
  obtain ⟨x,hx⟩ := exists_norm_eq H (show (0:ℝ)≤1 from zero_le_one)
  obtain ⟨f,hf,htr⟩ := exists_tracial_hull_of_norm_separable M x (hull_norm_separable M hfac hd hfin x)
  let τ := positive M x f hf
  have ht : ∀ a b : M,τ (a*b)=τ (b*a) := htr
  have hone : τ 1=1 := by
    change f 1=1
    rw [hull_one M x hf,hx]
    norm_num
  exact ⟨τ,ht,hull_normal M hfac hd hfin x hf,
    TraceDimension.faithful M τ ht hfac hd hfin hone,hone⟩

end Kadison.OrbitStateHull

end

end
end

end OAI
