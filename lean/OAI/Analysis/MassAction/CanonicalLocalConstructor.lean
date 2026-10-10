import OAI.Analysis.MassAction.TypeFamilyCertificate
import OAI.Analysis.MassAction.AffineLocalConstructor

namespace OAI

noncomputable section

namespace Problem326.Affine

/-- The lower-dimensional full certificates construct the canonical local
certificate in dimension `d`, with no additional existence hypothesis. -/
theorem localCertificate_of_lower_fullCertificates
    (d : ℕ) (hd : 0 < d)
    (ih : ∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate k a b E))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (_hab : a < b) (hE : ∀ r, Cube a b r → 0 < E r)
    (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    Nonempty (LocalCertificate d a b t E) := by
  have hE₀ : 0 < E (fun _ => t) := hE _ (fun _ => ⟨hat, htb⟩)
  by_cases htb' : t = b
  · subst t
    exact ⟨localCertificate_upper hd a b E hE₀⟩
  · have htb'' : t < b := lt_of_le_of_ne htb htb'
    apply localCertificate_of_layers hd htb'' E hE₀
    intro k hk hkd β htβ hβb
    obtain ⟨F, _, hF⟩ := exists_typeFamily_layerCertificate hk hkd htβ hβb E
      (fun r hr => hE r (fun i => ⟨hat.trans (hr i).1, (hr i).2⟩))
      (fun E' hE' => ih k hkd β b E' hβb hE')
    exact ⟨F, hF⟩

end Problem326.Affine

end

end OAI
