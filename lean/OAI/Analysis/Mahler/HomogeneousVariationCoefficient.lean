import OAI.Analysis.Mahler.WedgeEven
import OAI.Analysis.Mahler.HomogeneousDensityVariation

namespace OAI

namespace Mahler

lemma wedge_wedgePowerVariation_succ {Space : Type*} [AddCommGroup Space]
    [Module ℝ Space] [FiniteDimensional ℝ Space]
    (leadingForm : Space [⋀^Fin 1]→ₗ[ℝ] ℂ) (form variation : Space [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (degree : ℕ) :
    wedge leadingForm (wedgePowerVariation form variation (degree+1)) =
      ((degree+1 : ℕ) : ℂ) • wedge leadingForm
        (show Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ from
          wedge variation (wedgePower form degree)) := by
  let residual : Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ :=
    wedge variation (wedgePower form degree)
  calc
    _ = wedge leadingForm (((degree+1 : ℕ) : ℂ) • residual) :=
      congrArg (fun alternatingForm : Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ =>
        wedge leadingForm alternatingForm)
        (wedgePowerVariation_succ (Module.finBasis ℝ Space) form variation degree)
    _ = _ := wedge_smul_right _ leadingForm residual

/-- The residual with one explicit d beta factor and no suppressed placements.
The intermediate slot type keeps the original recursive order. -/
noncomputable def boundarySingleResidualFin {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1)+1)]→ₗ[ℝ] ℂ :=
  let B : ComplexEuclidean (k+2) [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ :=
    wedge (extDeriv (oneForm b) x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k)
  (wedge (oneForm a x).toAlternatingMap B).domDomCongr (boundaryFinEquiv (k+1))

/-- All residual placements combine with the positive multiplicity k+1.
The residual is retained; its integral is not assumed to vanish. -/
theorem boundaryResidualFin_succ {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    boundaryResidualFin (k := k+1) a b x =
      ((k+1 : ℕ) : ℂ) • boundarySingleResidualFin a b x := by
  have variationIdentity := wedge_wedgePowerVariation_succ (oneForm a x).toAlternatingMap
    (extDeriv (oneForm a) x).toAlternatingMap
    (extDeriv (oneForm b) x).toAlternatingMap k
  have reindexedIdentity := congrArg
    (fun form : ComplexEuclidean (k+2) [⋀^Fin 1 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
      form.domDomCongr (boundaryFinEquiv (k+1)))
    variationIdentity
  exact reindexedIdentity.trans (AlternatingMap.domDomCongr_smul _ _ _)

end Mahler

end OAI
