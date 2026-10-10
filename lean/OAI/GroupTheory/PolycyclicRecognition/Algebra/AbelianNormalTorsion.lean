import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFieldRank
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralTorsion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTorsionPowerSubgroup
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Field.ZMod

namespace OAI

/-! # Finite torsion for arbitrary abelian-by-abelian FP-infinity extensions -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra TensorProduct IsMulCommutative nonZeroDivisors
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

theorem abelian_normal_prime_reduction_finite (h : TypeFPInfinity G)
    (p : ℕ) (hp : p.Prime) : Finite (Additive N ⧸ integerMultiples (Additive N) p) := by
  let : Fact p.Prime := ⟨hp⟩
  let := abelian_normal_kernel_finite_field_rank N (ZMod p) h
  let : Finite (ZMod p ⊗[ℤ] Additive N) := Module.finite_of_finite (ZMod p)
  exact Finite.of_equiv _ (integerReductionEquiv (Additive N) p).toEquiv

theorem abelian_normal_integer_reduction_finite (h : TypeFPInfinity G)
    (n : ℕ) (hn : n ≠ 0) : Finite (Additive N ⧸ integerMultiples (Additive N) n) :=
  finite_integerReduction_of_primes (Additive N) (abelian_normal_prime_reduction_finite N h) n hn

theorem abelian_normal_kernel_torsion_finite (h : TypeFPInfinity G) :
    Finite (CommGroup.torsion N) := by
  let ρ := abelianKernelQuotientConjugationAction N
  let R := ℤ[G ⧸ N]
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let : Module.Finite R ρ.asModule := abelianKernelQuotient_finite N
  let : IsNoetherian R ρ.asModule := isNoetherian_of_isNoetherianRing_of_finite R ρ.asModule
  let e : ρ.asModule ≃ₗ[ℤ] Additive N := ρ.asModuleEquiv.toAddEquiv.toIntLinearEquiv
  have hp : ∀ p : ℕ, p.Prime → Finite (ρ.asModule ⧸ integerMultiples ρ.asModule p) := by
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    let := abelian_normal_kernel_finite_field_rank N (ZMod p) h
    let : Finite (ZMod p ⊗[ℤ] Additive N) := Module.finite_of_finite (ZMod p)
    let et : (ZMod p ⊗[ℤ] ρ.asModule) ≃ₗ[ℤ] (ZMod p ⊗[ℤ] Additive N) :=
      TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) e
    let : Finite (ZMod p ⊗[ℤ] ρ.asModule) := Finite.of_equiv _ et.symm.toEquiv
    exact Finite.of_equiv _ (integerReductionEquiv ρ.asModule p).toEquiv
  let T := Submodule.torsion' R ρ.asModule ℤ⁰
  let : Finite T := finite_integral_torsion_of_finite_reductions R ρ.asModule hp
  let F : CommGroup.torsion N → T := fun x => ⟨e.symm (Additive.ofMul (x : N)), by
    obtain ⟨n, hn, hxn⟩ := x.property.exists_pow_eq_one
    have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr hnZ⟩, ?_⟩
    change (n : ℤ) • e.symm (Additive.ofMul (x : N)) = 0
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, map_zero]
    simpa only [natCast_zsmul, ofMul_pow, ofMul_one] using congrArg Additive.ofMul hxn⟩
  apply Finite.of_injective F
  intro x y hxy
  apply Subtype.ext
  apply Additive.ofMul.injective
  apply e.symm.injective
  exact congrArg (fun a : T => (a : ρ.asModule)) hxy

theorem abelian_normal_kernel_characteristic_finiteIndex_torsionFree (h : TypeFPInfinity G) :
    ∃ K : Subgroup N, K.Characteristic ∧ K.FiniteIndex ∧ HasNoNontrivialTorsion K := by
  let := abelian_normal_kernel_torsion_finite N h
  let n := Nat.card (CommGroup.torsion N)
  have hn : n ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let := abelian_normal_integer_reduction_finite N h n hn
  exact ⟨(powMonoidHom n : N →* N).range, abelianPowerRange_characteristic N n,
    abelianPowerRange_finiteIndex N n, abelianPowerRange_torsionFree N⟩

end PolycyclicRecognition

end

end OAI
