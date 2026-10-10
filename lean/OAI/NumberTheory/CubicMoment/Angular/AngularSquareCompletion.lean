import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerFactorBounds
import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularHecke

namespace OAI

/-! The square of a fixed nonzero angular character is completed through
its own primitive conductor. The omitted Euler factors are retained. -/
noncomputable section
namespace CubicFirstMoment

lemma angularResidueIdealChar_square (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    angularResidueIdealChar q (χ^2) (2*ℓ) ν = (angularResidueIdealChar q χ ℓ ν)^2 := by
  unfold angularResidueIdealChar residueIdealChar
  rw [MulChar.pow_apply' χ (by norm_num : (2:ℕ)≠0)]
  rw [show 2*ℓ=ℓ+ℓ by ring,theta_add ℓ ℓ (idealExponentGenerator_ne_zero ν)]
  ring

lemma AngularUnitCompatible.square {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible q (χ^2) (2*ℓ) := by
  intro u
  rw [MulChar.pow_apply' χ (by norm_num : (2:ℕ)≠0)]
  rw [show 2*ℓ=ℓ+ℓ by ring,theta_add ℓ ℓ u.ne_zero]
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u)^2 := by ring
    _ = 1 := by rw [hu u]; norm_num

theorem angular_square_primitive_completion (hpub : PrimitiveAngularHeckeInput)
    {q : Eisenstein} (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (hu : AngularUnitCompatible q χ ℓ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ) (root : ℂ) (L Ldual : ℂ → ℂ),
      d ≠ 0 ∧ normNat d ≤ normNat q ∧ PrimitiveResidueCharacter d ψ ∧
      AngularUnitCompatible d ψ (2*ℓ) ∧ ‖root‖=1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar d ψ (2*ℓ)) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar d (star ψ) (-(2*ℓ))) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale d) (|((2*ℓ:ℤ):ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale d) (|((2*ℓ:ℤ):ℝ)|/2) L ∧
      Differentiable ℂ (fun s => idealEulerFactor (idealExponentOf q).support
        (angularResidueIdealChar d ψ (2*ℓ)) s*L s) ∧
      (∀ s : ℂ, 1 < s.re →
        idealEulerFactor (idealExponentOf q).support (angularResidueIdealChar d ψ (2*ℓ)) s*L s =
          normDirichletSeries (fun ν => (angularResidueIdealChar q χ ℓ ν)^2) idealExponentNorm s) := by
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq (χ^2)
  have hu2 := hi.angular_units hu.square
  have h2ℓ : 2*ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓ
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub (2*ℓ) d hd ψ hp hu2 (Or.inl h2ℓ)
  refine ⟨d,ψ,root,L,Ldual,hd,hN,hp,hu2,hr,hL,hs,hds,hFE,hcomp,
    (idealEulerFactor_differentiable _ _).mul hL,?_⟩
  intro s hss
  rw [hs s hss,←idealDirichlet_euler_exclusion _ _
    (angularResidueIdealChar_norm_le_one hd ψ (2*ℓ))
    (angularResidueIdealChar_add d ψ (2*ℓ)) hss]
  congr 1
  funext ν
  rw [←angularResidueIdealChar_square q χ ℓ ν]
  exact (induced_angularResidueIdealChar hq hi (2*ℓ) ν).symm

end CubicFirstMoment

end

end OAI
