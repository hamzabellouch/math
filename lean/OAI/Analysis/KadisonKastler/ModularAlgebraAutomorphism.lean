import OAI.Analysis.KadisonKastler.PublishedModularSpectral

namespace OAI

/-! # The modular automorphism group on the represented algebra -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

private def modularAlgebraHom (m : ModularSpectralResolution M Ω) (t : Multiplicative ℝ) :
    Algebra M →⋆ₐ[ℂ] Algebra M :=
  (((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (m.group t)).toStarAlgHom).comp
    M.toStarSubalgebra.subtype).codRestrict M.toStarSubalgebra (fun a => by
      change unitaryConj (m.group t) a.val ∈ M
      have h : unitaryConj (m.group t) a.val ∈
          unitaryConj (m.group t) '' (M : Set (H →L[ℂ] H)) := ⟨a.val, a.property, rfl⟩
      rwa [m.normalizes t] at h)

def modularAlgebraAut (m : ModularSpectralResolution M Ω) (t : Multiplicative ℝ) :
    Algebra M ≃⋆ₐ[ℂ] Algebra M := by
  apply StarAlgEquiv.ofBijective (modularAlgebraHom m t)
  constructor
  · intro a b hab
    apply Subtype.ext
    apply (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (m.group t)).injective
    exact congrArg Subtype.val hab
  · intro a
    have ha : a.val ∈ unitaryConj (m.group t) '' (M : Set (H →L[ℂ] H)) := by
      rw [m.normalizes t]
      exact a.property
    obtain ⟨b, hb, hba⟩ := ha
    exact ⟨⟨b, hb⟩, Subtype.ext hba⟩

theorem modularAlgebraAut_coe (m : ModularSpectralResolution M Ω) (t : Multiplicative ℝ)
    (a : Algebra M) : (modularAlgebraAut m t a).val = unitaryConj (m.group t) a.val := rfl

def modularAlgebraAction (m : ModularSpectralResolution M Ω) :
    Multiplicative ℝ →* (Algebra M ≃⋆ₐ[ℂ] Algebra M) where
  toFun := modularAlgebraAut m
  map_one' := by
    apply StarAlgEquiv.ext
    intro a
    apply Subtype.ext
    change unitaryConj (m.group 1) a.val = a.val
    rw [map_one, unitaryConj_one]
  map_mul' s t := by
    apply StarAlgEquiv.ext
    intro a
    apply Subtype.ext
    change unitaryConj (m.group (s * t)) a.val =
      unitaryConj (m.group s) (unitaryConj (m.group t) a.val)
    rw [map_mul, unitaryConj_mul]

theorem modularAlgebraAut_fixed (m : ModularSpectralResolution M Ω) (t : Multiplicative ℝ)
    (a : Algebra M) (ha : ProductStateCentralizes M Ω a.val) : modularAlgebraAut m t a = a := by
  apply Subtype.ext
  exact m.centralizer_fixed a.val a.property ha t

end

end KadisonKastler

end OAI
