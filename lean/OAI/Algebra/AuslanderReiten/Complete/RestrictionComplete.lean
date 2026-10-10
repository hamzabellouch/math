import OAI.Algebra.AuslanderReiten.Homology.RestrictionProjective
import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

def restrictRegularEquiv :
    R ≃ₗ[R] ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)) where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := e.map_add
  map_smul' a b := e.map_mul a b

theorem restrict_equiv_finite (M : ModuleCat.{u} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)) :=
    Module.Finite.equiv (restrictRegularEquiv e)
  exact restrict_finite e.toRingHom M

theorem restrict_equiv_projective (M : ModuleCat.{u} S)
    [Module.Finite S M] [Module.Projective S M] :
    Module.Projective R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : Module.Projective R ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)) :=
    Module.Projective.of_equiv (restrictRegularEquiv e)
  exact restrict_projective e.toRingHom M

theorem restrict_equiv_exactProjective (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (hK : ExactProjectiveCochain K) :
    ExactProjectiveCochain
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex _).obj K) where
  finite n := by
    let := hK.finite n
    exact restrict_equiv_finite e (K.X n)
  projective n := by
    let := hK.finite n
    let := hK.projective n
    exact restrict_equiv_projective e (K.X n)
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have he := hK.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at he
    ext x
    change x ∈ LinearMap.range (K.d (n-1) n).hom ↔
      x ∈ LinearMap.ker (K.d n (n+1)).hom
    rw [show LinearMap.range (K.d (n-1) n).hom =
      LinearMap.ker (K.d n (n+1)).hom from he]

theorem restrict_equiv_totallyAcyclic [Module.Injective R R]
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (hK : ExactProjectiveCochain K) :
    TotallyAcyclicComplex (CompleteComparison.chainOfCochain
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex _).obj K)) :=
  (restrict_equiv_exactProjective e K hK).to_chain.totallyAcyclic

end ArExplicit

end

end OAI
