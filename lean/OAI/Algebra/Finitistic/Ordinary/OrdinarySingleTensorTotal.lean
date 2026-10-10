import OAI.Algebra.Finitistic.Ordinary.OrdinarySingleTensorTerms

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.SingleBimoduleTensor
universe u
variable (k S A N : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (h₀ : p i₀ = 0)
open BimoduleComplexTensor

include hp h₀ in
theorem entry_selected_zero (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) (i : Fin l) :
    entry k S A (complex k S A N) Z p n i i₀ (z i) = 0 := by
  by_cases hi : i = i₀
  · subst i
    unfold entry
    rw [dite_eq_right (show ¬ p i₀ + 1 = p i₀ by omega)]
    rfl
  · have hs := otherTerm_subsingleton k S A N Z p hp i₀ h₀ n i hi
    rw [hs.elim (z i) 0,map_zero]

include hp h₀ in
theorem differential_selected (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) :
    differential k S A (complex k S A N) Z p n z i₀ =
      ((-(p i₀)).negOnePow • map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -(p i₀)) ((n+1) + -(p i₀)))) (z i₀) := by
  simp only [differential,LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply]
  rw [Finset.sum_eq_zero (fun i _ => entry_selected_zero k S A N Z p hp i₀ h₀ n z i),add_zero]

theorem termEquivAt_vertical (q : ℤ) (hq : q = 0) (n : ℤ)
    (y : term k S A (complex k S A N) Z q (n + -q)) :
    termEquivAt k S A N Z q hq (n+1)
      (((-q).negOnePow • map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -q) ((n+1) + -q))) y) =
    (((middleLeftComplex k S A N Z)⟦-q⟧).d n (n+1)).hom (termEquivAt k S A N Z q hq n y) := by
  change termEquivAt k S A N Z q hq (n+1)
      ((((-q).negOnePow : ℤ)) • (map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -q) ((n+1) + -q))) y) =
    (((-q).negOnePow : ℤ)) • (((middleLeftFunctor k S A N).map (Z.d (n + -q) ((n+1) + -q))).hom
      (termEquivAt k S A N Z q hq n y))
  rw [map_zsmul]
  congr 1
  exact congrArg (fun f => f y) (termEquivAt_map k S A N Z q hq n (n+1) (Z.d _ _))

theorem totalTermEquiv_differential (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) :
    totalTermEquiv k S A N Z p hp i₀ h₀ (n+1) (differential k S A (complex k S A N) Z p n z) =
    (((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).d n (n+1)).hom (totalTermEquiv k S A N Z p hp i₀ h₀ n z) := by
  change termEquivAt k S A N Z (p i₀) h₀ (n+1)
      (differential k S A (complex k S A N) Z p n z i₀) =
    (((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).d n (n+1)).hom (termEquivAt k S A N Z (p i₀) h₀ n (z i₀))
  rw [differential_selected k S A N Z p hp i₀ h₀]
  exact termEquivAt_vertical k S A N Z (p i₀) h₀ n (z i₀)

/-- A genuine ordinary bimodule in degree zero has exactly its ordinary tensor complex as total. -/
def shiftedTotalIso : total k S A (complex k S A N) Z p hp ≅ (middleLeftComplex k S A N Z)⟦-(p i₀)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalTermEquiv k S A N Z p hp i₀ h₀ n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have hd : (total k S A (complex k S A N) Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A (complex k S A N) Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A (complex k S A N) Z p n))
        (fun n => ModuleCat.ofHom (differential k S A (complex k S A N) Z p n)) n
    rw [hd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (totalTermEquiv_differential k S A N Z p hp i₀ h₀ n z).symm)

/-- Removing the proved zero shift identifies the ordinary tensor complex exactly. -/
def totalIso : total k S A (complex k S A N) Z p hp ≅ middleLeftComplex k S A N Z :=
  shiftedTotalIso k S A N Z p hp i₀ h₀ ≪≫
    (eqToIso (congrArg (fun q : ℤ => (middleLeftComplex k S A N Z)⟦q⟧) (show -(p i₀) = 0 by omega))) ≪≫
    (shiftFunctorZero (CochainComplex (ModuleCat.{u} S) ℤ) ℤ).app (middleLeftComplex k S A N Z)
end LittleFinitistic.SingleBimoduleTensor

end

end OAI
