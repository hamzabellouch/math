import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenRepresentation

namespace OAI

/-! Local uniqueness from two constructed comparison solutions and conserved
Wronskians. No global coefficient extension is required. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_unique_right (a b : ℝ) (hab : a≤b)
    (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b)) (q p : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hqD : ∀ t ∈ Ioo a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hpD : ∀ t ∈ Ioo a b, HasDerivAt p (spectralScalarField (V t) (p t)) t)
    (hinit : q a=p a) : q b=p b := by
  obtain ⟨D,hD,hDa,hDD⟩ := spectralScalar_local_exists a b hab V hV (1,0)
  obtain ⟨U,hU,hUa,hUD⟩ := spectralScalar_local_exists a b hab V hV (0,1)
  have hDD' (t : ℝ) (ht : t ∈ Ioo a b) := hDD t ⟨ht.1.le,ht.2.le⟩
  have hUD' (t : ℝ) (ht : t ∈ Ioo a b) := hUD t ⟨ht.1.le,ht.2.le⟩
  have hW := spectralScalarWronskian_eq a b hab V D U hD.continuousOn hU.continuousOn hDD' hUD'
  rw [hDa,hUa] at hW
  have hWb : spectralScalarWronskian (D b) (U b)=1 := by simpa only [spectralScalarWronskian,mul_one,mul_zero,sub_zero] using hW
  have hqU := spectralScalarWronskian_eq a b hab V q U hq hU.continuousOn hqD hUD'
  have hpU := spectralScalarWronskian_eq a b hab V p U hp hU.continuousOn hpD hUD'
  have hDq := spectralScalarWronskian_eq a b hab V D q hD.continuousOn hq hDD' hqD
  have hDp := spectralScalarWronskian_eq a b hab V D p hD.continuousOn hp hDD' hpD
  have he1 : spectralScalarWronskian (q b) (U b)=spectralScalarWronskian (p b) (U b) := by
    rw [hqU,hinit,hpU]
  have he2 : spectralScalarWronskian (D b) (q b)=spectralScalarWronskian (D b) (p b) := by
    rw [hDq,hinit,hDp]
  have hqd := spectralScalarWronskian_decomposition (D b) (U b) (q b) 1 one_ne_zero hWb
  have hpd := spectralScalarWronskian_decomposition (D b) (U b) (p b) 1 one_ne_zero hWb
  rw [he1,he2] at hqd
  exact hqd.symm.trans hpd

end DefocusingNLS

end OAI
