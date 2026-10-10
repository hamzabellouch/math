import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarUniqueness

namespace OAI

/-! Terminal uniqueness for the actual scalar comparison equation, using
the two normalized solutions and their conserved Wronskians. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_unique_left (a b : ℝ) (hab : a ≤ b)
    (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b)) (q p : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hqD : ∀ t ∈ Ioo a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hpD : ∀ t ∈ Ioo a b, HasDerivAt p (spectralScalarField (V t) (p t)) t)
    (hinit : q b = p b) : q a = p a := by
  obtain ⟨D,hD,hDa,hDD⟩ := spectralScalar_local_exists a b hab V hV (1,0)
  obtain ⟨U,hU,hUa,hUD⟩ := spectralScalar_local_exists a b hab V hV (0,1)
  have hqU := spectralScalarWronskian_eq a b hab V q U hq hU.continuousOn hqD
    (fun t ht => hUD t ⟨ht.1.le,ht.2.le⟩)
  have hpU := spectralScalarWronskian_eq a b hab V p U hp hU.continuousOn hpD
    (fun t ht => hUD t ⟨ht.1.le,ht.2.le⟩)
  have hDq := spectralScalarWronskian_eq a b hab V D q hD.continuousOn hq
    (fun t ht => hDD t ⟨ht.1.le,ht.2.le⟩) hqD
  have hDp := spectralScalarWronskian_eq a b hab V D p hD.continuousOn hp
    (fun t ht => hDD t ⟨ht.1.le,ht.2.le⟩) hpD
  have he1 : spectralScalarWronskian (q a) (U a) = spectralScalarWronskian (p a) (U a) := by
    rw [← hqU,← hpU,hinit]
  have he2 : spectralScalarWronskian (D a) (q a) = spectralScalarWronskian (D a) (p a) := by
    rw [← hDq,← hDp,hinit]
  rw [hUa] at he1
  rw [hDa] at he2
  apply Prod.ext
  · simpa [spectralScalarWronskian] using he1
  · simpa [spectralScalarWronskian] using he2

end DefocusingNLS

end OAI
