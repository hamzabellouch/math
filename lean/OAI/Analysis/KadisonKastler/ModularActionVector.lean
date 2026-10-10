import OAI.Analysis.KadisonKastler.ModularAlgebraAutomorphism
import OAI.Analysis.KadisonKastler.RegularCoreIntersection

namespace OAI

/-! # The vector implementation and strong continuity of the modular algebra action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} (m : ModularSpectralResolution M Ω)

theorem modularAlgebraAut_vector (t : Multiplicative ℝ) (a : Algebra M) :
    (modularAlgebraAut m t a).val Ω = (m.group t : H →L[ℂ] H) (a.val Ω) := by
  rw [modularAlgebraAut_coe]
  change (m.group t : H →L[ℂ] H) (a.val ((star (m.group t) : H →L[ℂ] H) Ω)) = _
  have hs : (star (m.group t) : H →L[ℂ] H) Ω = Ω := by
    have he : star (m.group t) = m.group t⁻¹ := by
      change (m.group t)⁻¹ = m.group t⁻¹
      exact (map_inv m.group t).symm
    rw [← Unitary.coe_star, he]
    exact m.isModular.fixes_vector _
  rw [hs]

theorem modularAlgebraAut_strongContinuous (a : Algebra M) (x : H) :
    Continuous (fun t : ℝ => (modularAlgebraAut m (Multiplicative.ofAdd t) a).val x) := by
  have hs (y : H) : Continuous (fun t : ℝ =>
      (star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H) y) := by
    simp_rw [← Unitary.coe_star, regularGroup_star_eq]
    exact (m.continuous y).comp continuous_neg
  change Continuous (fun t : ℝ => (m.group (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (a.val ((star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H) x)))
  exact continuous_unitary_field_apply _ m.continuous _ (a.val.continuous.comp (hs x))

end

end KadisonKastler

end OAI
