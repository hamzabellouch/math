import OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations

namespace OAI

noncomputable section

namespace PiExponent

namespace CoherentExtFiniteness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

structure PositiveCoherentFinitePresentation
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) where
  kernel : X.Modules
  kernel_coherent : kernel.IsFinitePresentation
  middle : X.Modules
  left : kernel ⟶ middle
  right : middle ⟶ M
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  middle_finite : ∀ q, 0 < q → letI := Module.compHom (cohomology middle q) (baseScalars p)
    FiniteDimensional ℂ (cohomology middle q)

theorem positive_coherent_cohomology_finite_of_presentations
    [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (l : ℕ) (hl : 0 < l) (U : Fin l → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (presentation : ∀ (M : X.Modules) [M.IsFinitePresentation],
      Nonempty (PositiveCoherentFinitePresentation p M))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  let := sheafComplexLinear p
  have hdown : ∀ k q, 0 < q → l ≤ q + k →
      ∀ (A : X.Modules) [A.IsFinitePresentation], Module.Finite ℂ (cohomology A q) := by
    intro k
    induction k with
    | zero =>
      intro q hq hbound A hA
      let : A.IsQuasicoherent :=
        (SheafOfModules.IsFinitePresentation.exists_quasicoherentData A).choose.isQuasicoherent
      have hz : ∀ x : cohomology A q, x = 0 :=
        PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover A q (by omega)
      let : Subsingleton (cohomology A q) := ⟨fun x y => (hz x).trans (hz y).symm⟩
      infer_instance
    | succ k ih =>
      intro q hq hbound A hA
      let P := Classical.choice (presentation A)
      let S := ShortComplex.mk P.left P.right P.comp_zero
      let : P.kernel.IsFinitePresentation := P.kernel_coherent
      let : Module.Finite ℂ (Ext.{1} (structureSheaf X) S.X₂ q) := by
        change @Module.Finite ℂ (cohomology P.middle q) _ _ (complexExtModule p P.middle q)
        rw [complexExtModule_eq]
        exact P.middle_finite q hq
      let : Module.Finite ℂ (Ext.{1} (structureSheaf X) S.X₁ (q+1)) :=
        ih (q+1) (by omega) (by omega) P.kernel
      exact finite_middle_of_exact
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := ℂ) (structureSheaf X) (S := S) q)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := ℂ) (structureSheaf X) P.shortExact q)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := ℂ) (structureSheaf X) P.shortExact q)
  have hf := hdown l q hq (Nat.le_add_left _ _) M
  change @Module.Finite ℂ (cohomology M q) _ _ (complexExtModule p M q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

end CoherentExtFiniteness

namespace NegativeTwistPresentations
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def positiveCoherentFinitePresentation [IsLocallyNoetherian X]
    (L N : LineBundle X) {M : X.Modules} [M.IsFinitePresentation] {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections) [s.IsFiniteType]
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (hN : ∀ q, 0 < q → letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    CoherentExtFiniteness.PositiveCoherentFinitePresentation p M where
  kernel := kernel (presentationMap L N s e)
  kernel_coherent := kernel_isFinitePresentation L N s e
  middle := moduleTensor X (SheafOfModules.free s.I) N.sheaf
  left := kernel.ι (presentationMap L N s e)
  right := presentationMap L N s e
  comp_zero := kernel.condition (presentationMap L N s e)
  shortExact := presentation_shortExact L N s e
  middle_finite := fun q hq => middle_cohomology_finite L N s p q (hN q hq)

end NegativeTwistPresentations

end PiExponent

end

end OAI
