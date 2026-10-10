import OAI.Analysis.MassAction.AffineCertificates
import OAI.Analysis.MassAction.AffineLocalization

namespace OAI

noncomputable section

open Filter Topology

namespace Problem326.Affine

/-- A fixed full affine certificate gives a uniform activity bound on its
exponent cube at all sufficiently small positive scales. -/
theorem FullCertificate.uniform_activity {d : ℕ} {a b : ℝ}
    {E : (Fin d → ℝ) → ℝ} (C : FullCertificate d a b E) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ p : Fin d → ℝ, Cube a b p → ∀ L ∈ C.labels,
        Active C.labels L h (powerPoint h p) → ‖p - L.slope‖ < E L.slope := by
  classical
  let ι := {L : Label d // L ∈ C.labels}
  let active : ι → ℝ → (Fin d → ℝ) → Prop :=
    fun L h p => Active C.labels L.val h (powerPoint h p)
  obtain ⟨h0, hh0, huniform⟩ := Problem326.finite_uniform_activity_of_asymptotic
    (K := Set.Icc (fun _ : Fin d => a) (fun _ => b)) isCompact_Icc
    active (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p hp hact
      obtain ⟨h, q, hhpos, hhlim, hqlim, hactive⟩ := hact.exists_sequences
      exact C.approximation L.val L.property h q p hhpos hhlim hqlim
        (fun i => ⟨hp.1 i, hp.2 i⟩) hactive)
  refine ⟨h0, hh0, ?_⟩
  intro h hhpos hhsmall p hp L hL hact
  exact huniform h hhpos hhsmall ⟨L, hL⟩ p
    ⟨fun i => (hp i).1, fun i => (hp i).2⟩ hact

end Problem326.Affine

end

end OAI
