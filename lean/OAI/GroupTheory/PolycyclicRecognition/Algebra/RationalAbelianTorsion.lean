import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalZeroCoefficientHomology
import Mathlib.RingTheory.Localization.BaseChange

namespace OAI

/-! # Rationalization detects torsion in abelian groups -/
noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
variable {A : Type} [CommGroup A]

theorem rational_module_isZero_of_surjective {M P : Type}
    [AddCommGroup M] [AddCommGroup P] [Module ℤ M] [Module ℤ P]
    (f : M →ₗ[ℤ] P) (hf : Function.Surjective f)
    (hM : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] M))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] P)) := by
  let fQ := ModuleCat.ofHom (f.baseChange ℚ)
  let : Epi fQ := (ModuleCat.epi_iff_surjective fQ).mpr (f.baseChange_surjective ℚ hf)
  exact IsZero.of_epi fQ hM

theorem rationalAbelianMap_eq_zero_iff_isOfFinOrder (a : A) :
    rationalAbelianMap (Additive.ofMul a) = 0 ↔ IsOfFinOrder a := by
  change (TensorProduct.mk ℤ ℚ (Additive A) 1) (Additive.ofMul a) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)]
  constructor
  · rintro ⟨z, hz⟩
    apply isOfFinOrder_iff_zpow_eq_one.mpr
    refine ⟨(z : ℤ), mem_nonZeroDivisors_iff_ne_zero.mp z.property, ?_⟩
    exact congrArg Additive.toMul hz
  · intro ha
    obtain ⟨n, hn, hpow⟩ := ha.exists_pow_eq_one
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by omega)⟩, ?_⟩
    change (n : ℤ) • Additive.ofMul a = 0
    have he := congrArg Additive.ofMul hpow
    change n • Additive.ofMul a = 0 at he
    simpa only [natCast_zsmul] using he

theorem rationalAbelianSpace_isZero_iff_torsion :
    IsZero (ModuleCat.of ℚ (RationalAbelianSpace A)) ↔ ∀ a : A, IsOfFinOrder a := by
  constructor
  · intro h a
    let : Subsingleton (RationalAbelianSpace A) := ModuleCat.subsingleton_of_isZero h
    exact (rationalAbelianMap_eq_zero_iff_isOfFinOrder a).mp (Subsingleton.elim _ _)
  · intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [hx, hy, add_zero]
    | tmul q a =>
      have ha := (rationalAbelianMap_eq_zero_iff_isOfFinOrder a.toMul).mpr (h a.toMul)
      change (1 : ℚ) ⊗ₜ[ℤ] a = 0 at ha
      have he := congrArg (fun x : RationalAbelianSpace A => q • x) ha
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_zero] using he

end PolycyclicRecognition

end

end OAI
