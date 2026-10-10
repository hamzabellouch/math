import OAI.Analysis.MassAction.AffineCertificates
import OAI.Analysis.MassAction.AffineLocalBand
import OAI.Analysis.MassAction.UniformOffsetDecay

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem326.Affine

/-- A fixed-minimum certificate supplies a common neighborhood radius with
both approximation throughout the band and the stronger offset decay used
by the interval-gluing construction. -/
theorem LocalCertificate.exists_radius
    {d : ℕ} (hd : 0 < d) {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (C : LocalCertificate d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ L ∈ C.labels,
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ (t + ρ))) ∧
      ∀ s : ℝ, |s - t| < ρ → ApproximatesAtMinimum C.labels a b s E := by
  classical
  obtain ⟨ρ₀, hρ₀, hnear⟩ := approximatesAtMinimum_nearby
    hd C.labels a b t E C.approximation
  let : Nonempty C.labels := ⟨⟨_, C.baseline⟩⟩
  have hdecay (L : C.labels) : ∃ β : ℝ, t < β ∧
      L.val.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β) :=
    ⟨C.decayExponent, C.decay_gt, (C.offsets L.val L.property).isBigO⟩
  obtain ⟨ρ, hρ, hρsmall, hoffsets⟩ := exists_radius_with_offset_decay
    (fun L : C.labels => L.val.offset) t ρ₀ hρ₀ hdecay
  refine ⟨ρ, hρ, (fun L hL => hoffsets ⟨L, hL⟩), ?_⟩
  intro s hs
  apply hnear s
  have h := abs_lt.mp (hs.trans hρsmall)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Problem326.Affine

end

end OAI
