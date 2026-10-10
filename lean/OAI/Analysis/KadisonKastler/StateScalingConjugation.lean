import OAI.Analysis.KadisonKastler.StateScalingGraph

namespace OAI

/-! # The modular conjugation identity for scaling operators -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H} {r : ℝ}

namespace StateScales

theorem polarCoordinates_eq (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    (tomitaPolarCoordinates J Ω hsep hcyc (v.val Ω)).val =
      (Real.sqrt (r/(1+r)) : ℂ) • rescaledGraphVector J Ω 1 v.val := by
  have ht : 0 < r/(1+r) := div_pos hr (by linarith)
  have hk : (Real.sqrt (r/(1+r)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 ht))
  apply smul_right_injective (M := TomitaGraphHilbert H) hk
  change (Real.sqrt (r/(1+r)) : ℂ) •
      (tomitaPolarCoordinates J Ω hsep hcyc (v.val Ω)).val =
    (Real.sqrt (r/(1+r)) : ℂ) •
      ((Real.sqrt (r/(1+r)) : ℂ) • rescaledGraphVector J Ω 1 v.val)
  rw [hv.polarCoordinates J hsep hcyc v hr,smul_smul]
  congr 1
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt ht.le]

theorem polarConjugation (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    tomitaPolarConjugation J Ω hsep hcyc (v.val Ω) =
      (Real.sqrt r : ℂ) • (star v.val Ω) := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  have hstar : StateScales M Ω r⁻¹ (star v).val := hv.adjoint (ne_of_gt hr)
  have hratio : r/(1+r) = r*(r⁻¹/(1+r⁻¹)) := by
    have h1 : 1+r ≠ 0 := ne_of_gt (by linarith)
    have h2 : 1+r⁻¹ ≠ 0 := ne_of_gt (by positivity)
    field_simp [ne_of_gt hr,h1,h2]
    ring
  have hsqrt : Real.sqrt (r/(1+r)) = Real.sqrt r * Real.sqrt (r⁻¹/(1+r⁻¹)) := by
    rw [hratio,Real.sqrt_mul hr.le]
  apply U.injective
  rw [map_smul,tomitaPolarCoordinates_conjugation]
  apply Subtype.ext
  change tomitaGraphFlip J (U (v.val Ω)).val =
    (Real.sqrt r : ℂ) • (U ((star v).val Ω)).val
  rw [hv.polarCoordinates_eq J hsep hcyc v hr,
    (tomitaGraphFlip J).map_smulₛₗ,Complex.conj_ofReal,tomitaGraphFlip_vector J Ω v,
    hstar.polarCoordinates_eq J hsep hcyc (star v) (inv_pos.mpr hr),smul_smul]
  congr 1
  simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hsqrt

theorem polarConjugation_adjoint (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    (Real.sqrt r : ℂ) • tomitaPolarConjugation J Ω hsep hcyc (star v.val Ω) = v.val Ω := by
  have he := congrArg (tomitaPolarConjugation J Ω hsep hcyc)
    (hv.polarConjugation J hsep hcyc v hr)
  rw [tomitaPolarConjugation_involutive,
    (tomitaPolarConjugation J Ω hsep hcyc).map_smulₛₗ,Complex.conj_ofReal] at he
  exact he.symm

end StateScales

end

end KadisonKastler

end OAI
