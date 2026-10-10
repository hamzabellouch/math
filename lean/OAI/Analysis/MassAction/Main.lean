import OAI.Analysis.MassAction.ActiveBranchMinimum
import OAI.Analysis.MassAction.AffineApproximation
import OAI.Analysis.MassAction.AffineCertificateBridge
import OAI.Analysis.MassAction.AffineCertificates
import OAI.Analysis.MassAction.AffineExistence
import OAI.Analysis.MassAction.AffineGlobalGluing
import OAI.Analysis.MassAction.AffineGluing
import OAI.Analysis.MassAction.AffineLayers
import OAI.Analysis.MassAction.AffineLimitSet
import OAI.Analysis.MassAction.AffineNeighborhood
import OAI.Analysis.MassAction.AffinePolytope
import OAI.Analysis.MassAction.AffineSignGap
import OAI.Analysis.MassAction.AffineTrajectory
import OAI.Analysis.MassAction.BarrierInvariance
import OAI.Analysis.MassAction.ClampExtension
import OAI.Analysis.MassAction.CompactBounds
import OAI.Analysis.MassAction.CompactContinuation
import OAI.Analysis.MassAction.CompactInvariance
import OAI.Analysis.MassAction.CompleteAffine
import OAI.Analysis.MassAction.CutDecomposition
import OAI.Analysis.MassAction.CutFlux
import OAI.Analysis.MassAction.FiniteMinimum
import OAI.Analysis.MassAction.FirstExit
import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.FixedMinimumCertificate
import OAI.Analysis.MassAction.FixedMinimumEstimates
import OAI.Analysis.MassAction.GlueCurves
import OAI.Analysis.MassAction.IntervalChain
import OAI.Analysis.MassAction.IntervalGluing
import OAI.Analysis.MassAction.LabelTrajectory
import OAI.Analysis.MassAction.LayerSequence
import OAI.Analysis.MassAction.LocalExistence
import OAI.Analysis.MassAction.MassActionFlux
import OAI.Analysis.MassAction.MassActionRegularity
import OAI.Analysis.MassAction.Model
import OAI.Analysis.MassAction.MonomialOrder
import OAI.Analysis.MassAction.NetworkApproximation
import OAI.Analysis.MassAction.NetworkBarrier
import OAI.Analysis.MassAction.ODEConcatenation
import OAI.Analysis.MassAction.ODEGlobal
import OAI.Analysis.MassAction.ODEUniqueness
import OAI.Analysis.MassAction.PlateauCertificate
import OAI.Analysis.MassAction.PlateauGeometry
import OAI.Analysis.MassAction.PolyhedronGeometry
import OAI.Analysis.MassAction.PowerAsymptotics
import OAI.Analysis.MassAction.SignTolerance
import OAI.Analysis.MassAction.SmallParameter
import OAI.Analysis.MassAction.SolutionUniqueness
import OAI.Analysis.MassAction.UniformActivity
import OAI.Analysis.MassAction.UniformAffineData
import OAI.Analysis.MassAction.UniformOffsetDecay

namespace OAI

noncomputable section

namespace Problem326

theorem compact_convex_invariant_polytope :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ K : Set (Fin d → ℝ),
        IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
        x0 ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  intro d N κ _ hweak hκ x0 hx0
  apply BarrierConstruction.compact_convex_invariant_polytope_of_uniform ?_
    N κ hweak hκ x0 hx0
  exact Affine.uniform_affine_data_of_full_certificates
    (fun E hE => Affine.exists_fullCertificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

theorem global_bounded_persistent_solution :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  intro d N κ hd hweak hκ x0 hx0
  obtain ⟨K, hK, _, _, hxK, hpos, hinv⟩ :=
    compact_convex_invariant_polytope d N κ hd hweak hκ x0 hx0
  exact global_bounds_of_compact_invariant N κ x0 hK hxK hpos hinv

end Problem326

end

end OAI
