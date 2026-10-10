import OAI.Algebra.Finitistic.Ordinary.OrdinaryComplexTensorMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

theorem transport_d {q q' r r' : ℤ} (hq : q=q') (hr : r=r') :
    eqToHom (congrArg Z.X hq) ≫ Z.d q' r' = Z.d q r ≫ eqToHom (congrArg Z.X hr) := by
  subst q'
  subst r'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

/-- Signed vertical tensor differential on the concrete balanced tensor term. -/
def vertical (n p : ℤ) : term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p ((n+1) + -p) :=
  (-p).negOnePow • map k A Q Z (𝟙 (Q.X p)) (Z.d (n + -p) ((n+1) + -p))

/-- The two mixed terms cancel with the actual integer total-complex signs. -/
theorem horizontal_mixed (n p p' : ℤ) (h : p+1=p') :
    (vertical k A Q Z (n+1) p').comp (horizontal k A Q Z n p p' h) +
      (horizontal k A Q Z (n+1) p p' h).comp (vertical k A Q Z n p) = 0 := by
  unfold vertical horizontal
  rw [LinearMap.smul_comp,LinearMap.comp_smul,map_comp,map_comp,Category.comp_id,Category.id_comp]
  have hd := transport_d A Z
    (show n + -p = (n+1) + -p' by omega)
    (show (n+1) + -p = ((n+1)+1) + -p' by omega)
  rw [hd]
  have hs : (-p').negOnePow = -(-p).negOnePow := by
    subst p'
    simp only [Int.negOnePow_neg,Int.negOnePow_succ]
  rw [hs]
  change (-(↑((-p).negOnePow) : ℤ)) • _ + (↑((-p).negOnePow) : ℤ) • _ = (0 : term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p' (((n+1)+1) + -p'))
  rw [neg_smul,neg_add_cancel]
end LittleFinitistic.ComplexTensor

end

end OAI
