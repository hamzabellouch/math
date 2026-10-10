import OAI.Analysis.MassAction.AffineGlobalAssembly
import OAI.Analysis.MassAction.AffineCertificates

namespace OAI

noncomputable section

namespace Problem326.Affine

/-- The complete gluing argument in the exact certificate interface consumed by
`fullCertificate_of_local_and_glue`. No gluing assumption remains in this theorem. -/
theorem fullCertificate_glue
    (d : ℕ) (hd : 0 < d) (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (hab : a < b) (_hE : ∀ r, Cube a b r → 0 < E r)
    (hlocal : ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) :
    Nonempty (FullCertificate d a b E) := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨Λ, hne, hprop, happ⟩ := exists_global_family_of_fixedMinimum hab.le E (by
    intro t ht
    let C := Classical.choice (hlocal t ht.1 ht.2)
    refine ⟨C.labels, C.baseline, ?_, ?_, ?_, C.approximation⟩
    · intro L hL i
      exact ⟨ht.1.trans (C.slopes L hL i).1, (C.slopes L hL i).2⟩
    · intro L hL i
      exact (C.slopes L hL i).1
    · intro L hL
      exact ⟨C.decayExponent, C.decay_gt, (C.offsets L hL).isBigO⟩)
  exact ⟨{
    labels := Λ
    nonempty := hne
    slopes := fun L hL => (hprop L hL).1
    offsets := fun L hL => (hprop L hL).2
    approximation := happ
  }⟩

/-- The full affine approximation theorem now reduces solely to constructing
fixed-minimum certificates from lower-dimensional full certificates. -/
theorem fullCertificate_of_local_constructor
    (construct : ∀ d : ℕ, 0 < d →
      (∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate k a b E)) →
      ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) →
        ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate d a b E) :=
  fullCertificate_of_local_and_glue construct fullCertificate_glue

end Problem326.Affine

end

end OAI
