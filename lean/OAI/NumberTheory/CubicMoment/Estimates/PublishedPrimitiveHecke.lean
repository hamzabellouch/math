import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
import OAI.NumberTheory.CubicMoment.Estimates.HeckeSmoothApproximation

namespace OAI

/-! The classical primitive Hecke input on the actual finite residue
characters constructed here. Completion/functional equation: Watkins
(2011), §3.6, p.123; entire order-one completion: Thorner–Zaman (2019),
§2C, p.1049, Eq.(2-15). This is a conditional input, not an axiom.
No character sum estimate or new-paper conclusion is included. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def residueHeckeScale (q : Eisenstein) : ℝ := Real.sqrt (3*norm q)/(2*Real.pi)

lemma residueHeckeScale_pos {q : Eisenstein} (hq : q ≠ 0) : 0 < residueHeckeScale q := by
  unfold residueHeckeScale
  positivity [norm_pos_of_ne_zero hq,Real.pi_pos]

/-- The standard analytic continuation and functional equation for a
primitive nonprincipal finite Hecke character with trivial infinity type.
The two Dirichlet series are literally those of the residue character
and its complex conjugate on the complete ideal exponent lattice. -/
def PrimitiveResidueHeckeInput : Prop :=
  ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → χ ≠ 1 →
    (∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) →
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L

/-- The published continuation/functional-equation input supplies the
analytic properties of the primitive residue character. The growth
needed for contour shifts follows by the Phragmén–Lindelöf theorem. -/
theorem primitive_residue_analytic_data (hpub : PrimitiveResidueHeckeInput)
    {q : Eisenstein} (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) (hn : χ ≠ 1)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (hGamma : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧
      PrimitiveHeckeAnalyticData (residueIdealChar q χ) (residueIdealChar q (star χ))
        (residueHeckeScale q) root L Ldual := by
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub q hq χ hp hn hu
  exact ⟨root,L,Ldual,hr,primitiveHeckeAnalyticData_of_completed
    (residueIdealChar_norm_le_one hq χ) (residueIdealChar_norm_le_one hq (star χ))
    (residueHeckeScale_pos hq) hL hs hds hFE hcomp hGamma⟩

/-- An actual primitive residue character has the full smooth dual
approximation with a uniform error, from the published input above and
the explicit weak Gamma bounds. -/
theorem primitive_residue_smooth_approximation (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Eisenstein), q ≠ 0 →
      ∀ χ : MulChar (Residues q) ℂ, PrimitiveResidueCharacter q χ → χ ≠ 1 →
      (∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) →
      ∃ root : ℂ, ‖root‖ = 1 ∧ ∀ (Y Z J t : ℝ),
      1 ≤ Y → 1 ≤ Z → 0 < J → Z ≤ Y^H → J ≤ Y^H →
      ((residueHeckeScale q)^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖(∑' ν, residueIdealChar q χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-
        retainedHeckeIntegral W (residueIdealChar q (star χ)) root (residueHeckeScale q) Z J t‖ ≤ C*Y^(-R) := by
  obtain ⟨C,hC,happrox⟩ := hecke_smooth_approximation_of_completed W hW hpos hsm hδ H R
  refine ⟨C,hC,?_⟩
  intro q hq χ hp hn hu
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub q hq χ hp hn hu
  refine ⟨root,hr,?_⟩
  intro Y Z J t hY hZ hJ hZH hJH hcut
  exact happrox (residueIdealChar q χ) (residueIdealChar q (star χ))
    (residueIdealChar_norm_le_one hq χ) (residueIdealChar_norm_le_one hq (star χ))
    root hr.le Y (residueHeckeScale q) Z J t hY (residueHeckeScale_pos hq) hZ hJ
    hZH hJH hcut L Ldual hL hs hds hFE hcomp hGI hGQ

end CubicFirstMoment

end

end OAI
