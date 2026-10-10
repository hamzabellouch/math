import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalForget
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalFunctor

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def termInputMap (r q : ℤ) : term k S A Q Z r q →ₗ[S] term k S A Q Z' r q :=
  LeftTensor.bimap (N := ComplexTensor.leftTerm k A Z q) (N' := ComplexTensor.leftTerm k A Z' q)
    (BimoduleCoefficients.map k S A (𝟙 (Q.X r)))
    (BimoduleCoefficients.map_left k S A (𝟙 (Q.X r))) (f.f q).hom

theorem termInputMap_id (Z : CochainComplex (ModuleCat.{u} A) ℤ) (r q : ℤ) :
    termInputMap k S A Q (𝟙 Z) r q = LinearMap.id := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x y
  rfl

theorem termInputMap_comp {Z'' : CochainComplex (ModuleCat.{u} A) ℤ} (g : Z' ⟶ Z'') (r q : ℤ) :
    termInputMap k S A Q (f ≫ g) r q =
      (termInputMap k S A Q g r q).comp (termInputMap k S A Q f r q) := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x y
  rfl

def totalInputMap (n : ℤ) : totalTerm k S A Q Z p n →ₗ[S] totalTerm k S A Q Z' p n :=
  LinearMap.pi (fun i => (termInputMap k S A Q f (p i) (n + -(p i))).comp (LinearMap.proj i))

/-- The retained-action input map is exactly the prior tensor map after forgetting. -/
theorem forget_totalInputMap (n : ℤ) (z : totalTerm k S A Q Z p n) :
    forgetTotalEquiv k S A Q Z' p n (totalInputMap k S A Q f p n z) =
      ((ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f).f n).hom
        (forgetTotalEquiv k S A Q Z p n z) := by
  funext i
  rw [ComplexTensor.finiteTotalMap_apply]
  change forgetEquiv k S A Q Z' (p i) (n + -(p i))
      (termInputMap k S A Q f (p i) (n + -(p i)) (z i)) =
    ComplexTensor.inputMap k A (rightComplex k S A Q) f (p i) (n + -(p i))
      (forgetEquiv k S A Q Z (p i) (n + -(p i)) (z i))
  let L := (forgetEquiv k S A Q Z' (p i) (n + -(p i))).toLinearMap.comp
    ((termInputMap k S A Q f (p i) (n + -(p i))).restrictScalars k)
  let R := (ComplexTensor.inputMap k A (rightComplex k S A Q) f (p i) (n + -(p i))).comp
    (forgetEquiv k S A Q Z (p i) (n + -(p i))).toLinearMap
  change L (z i) = R (z i)
  induction z i using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht x y => rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

include hp in
theorem totalInputMap_comm (n : ℤ) :
    (differential k S A Q Z' p n).comp (totalInputMap k S A Q f p n) =
      (totalInputMap k S A Q f p (n+1)).comp (differential k S A Q Z p n) := by
  apply LinearMap.ext
  intro z
  apply (forgetTotalEquiv k S A Q Z' p (n+1)).injective
  change forgetTotalEquiv k S A Q Z' p (n+1)
      (differential k S A Q Z' p n (totalInputMap k S A Q f p n z)) =
    forgetTotalEquiv k S A Q Z' p (n+1)
      (totalInputMap k S A Q f p (n+1) (differential k S A Q Z p n z))
  rw [forget_differential k S A Q Z' p hp,forget_totalInputMap k S A Q f p hp,
    forget_totalInputMap k S A Q f p hp,forget_differential k S A Q Z p hp]
  have h := congrArg (fun g => g.hom (forgetTotalEquiv k S A Q Z p n z))
    ((ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f).comm n (n+1))
  dsimp only [ComplexTensor.finiteTotal,FiniteColumnComplex.total] at h
  rw [FiniteColumnComplex.complex_d,FiniteColumnComplex.complex_d] at h
  exact h

/-- Actual chain maps of the outside-action tensor total. -/
def totalMap : total k S A Q Z p hp ⟶ total k S A Q Z' p hp where
  f n := ModuleCat.ofHom (totalInputMap k S A Q f p n)
  comm' n m h := by
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (total k S A Q Z' p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z' p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z' p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z' p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    exact totalInputMap_comm k S A Q f p hp n

theorem forgetTotalIso_natural :
    ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).map
      (totalMap k S A Q f p hp) ≫ (forgetTotalIso k S A Q Z' p hp).hom =
    (forgetTotalIso k S A Q Z p hp).hom ≫
      ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact forget_totalInputMap k S A Q f p hp n z
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
