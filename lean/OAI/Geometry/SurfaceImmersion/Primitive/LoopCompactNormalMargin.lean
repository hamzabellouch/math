import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicNormalStability

namespace OAI

/-! A single positive normal margin for the whole compact set of admissible
low jets, before choosing a slow map or a fast scale. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem compact_normal_margin {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ J ∈ Q, ∀ t : ℝ, ∀ H : VelocityFrame.NormalTriple,
      ‖H-![VelocityFrame.leadingTangent (slot 1 J) (slot 2 J) (slot 6 J)
        (l.velocity (J,t)),slot 2 J,slot 6 J]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let X : Q → NormalFrame.Vec := fun J => slot 1 J
  let Y : Q → NormalFrame.Vec := fun J => slot 2 J
  let C : Q → NormalFrame.Vec := fun J => slot 6 J
  let V : Q → C(Period,NormalFrame.Vec) := fun J =>
    ⟨fun t => spaceCoordinates (l.euclideanVelocity J t),
      spaceCoordinates.continuous.comp (l.euclideanVelocity J).continuous⟩
  have hX : Continuous X := (slot_smooth 1).continuous.comp continuous_subtype_val
  have hY : Continuous Y := (slot_smooth 2).continuous.comp continuous_subtype_val
  have hC : Continuous C := (slot_smooth 6).continuous.comp continuous_subtype_val
  have hV : Continuous (fun p : Q × ℝ => V p.1 (p.2 : Period)) := by
    have hi : Continuous (fun p : Q × ℝ => ((p.1 : LowJet),p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact spaceCoordinates.continuous.comp
      (l.euclideanVelocity_smooth.continuousOn.comp_continuous hi
        (fun p => ⟨hQO p.1.property,mem_univ _⟩))
  have hVeq (J : Q) (t : ℝ) : V J (t : Period) = l.velocity (J,t) := by
    change spaceCoordinates (l.euclideanVelocity J (t : Period)) = _
    rw [l.euclideanVelocity_apply (hQO J.property)]
    exact spaceCoordinates.apply_symm_apply _
  have hYV : ∀ J ∈ (univ : Set Q), ∀ t : Period, Y J ⬝ᵥ V J t = 0 := by
    intro J _ t
    refine Quotient.inductionOn' t ?_
    intro t
    rw [hVeq]
    exact l.perpY J (hQO J.property) t
  have hCV : ∀ J ∈ (univ : Set Q), ∀ t : Period, C J ⬝ᵥ V J t = 0 := by
    intro J _ t
    refine Quotient.inductionOn' t ?_
    intro t
    rw [hVeq]
    exact l.perpC J (hQO J.property) t
  have hV0 : ∀ J ∈ (univ : Set Q), ∀ t : Period, V J t ≠ 0 := by
    intro J _ t ht
    change spaceCoordinates (l.euclideanVelocity J t) = 0 at ht
    have he : l.euclideanVelocity J t = 0 := spaceCoordinates.injective
      (by simpa only [map_zero] using ht)
    have hh := l.euclideanVelocity_length (hQO J.property) t
    rw [he,inner_zero_left] at hh
    exact (ne_of_gt (l.q_pos (hQO J.property))) hh.symm
  obtain ⟨ε,c,hε,hc,hh⟩ := VelocityFrame.periodic_leading_normal_stability
    (isCompact_univ : IsCompact (univ : Set Q)) hX hY hC V hV
    (fun J _ => l.gram_ne J (hQO J.property)) hYV hCV hV0
  refine ⟨ε,c,hε,hc,?_⟩
  intro J hJ t H hH
  apply hh ⟨J,hJ⟩ (mem_univ _) t H
  simpa only [X,Y,C,hVeq] using hH

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
