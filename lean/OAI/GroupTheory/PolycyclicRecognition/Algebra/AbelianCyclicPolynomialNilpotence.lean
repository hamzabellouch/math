import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicUnipotentNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerConjugationUnipotent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicPowerIndex

namespace OAI

/-! # Polynomial-growth cyclic extensions of free abelian groups

The action has a unipotent positive power. Its powered semidirect product is
nilpotent and embeds as an actual subgroup of finite index in the given group.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N A : Type} [Group N] [AddCommGroup A]

def cyclicSemidirectKernelEquiv (a : MulAut N) :
    N ≃* (SemidirectProduct.rightHom :
      (N ⋊[integerPowerAction a] Multiplicative ℤ) →* Multiplicative ℤ).ker :=
  MulEquiv.ofBijective
    ((SemidirectProduct.inl : N →* N ⋊[integerPowerAction a] Multiplicative ℤ).codRestrict
      _ (fun x => SemidirectProduct.rightHom_inl x)) ⟨by
        intro x y h
        exact congrArg (fun z => z.val.left) h,
      by
        intro x
        refine ⟨x.val.left, ?_⟩
        apply Subtype.ext
        refine SemidirectProduct.ext ?_ ?_
        · rfl
        · exact x.property.symm⟩

theorem semidirect_abelian_nilpotent_of_unipotent
    (a : MulAut N) (f : N →* Multiplicative A) (hf : Function.Injective f)
    (T : Module.End ℤ A) (hT : ∀ x, (f (a x)).toAdd = T (f x).toAdd)
    (hnil : IsNilpotent (T - 1)) :
    Group.IsNilpotent (N ⋊[integerPowerAction a] Multiplicative ℤ) := by
  let q := (SemidirectProduct.rightHom :
    (N ⋊[integerPowerAction a] Multiplicative ℤ) →* Multiplicative ℤ)
  let e := cyclicSemidirectKernelEquiv a
  let F := f.comp e.symm.toMonoidHom
  have hF : Function.Injective F := hf.comp e.symm.injective
  let : IsMulCommutative q.ker := ⟨⟨fun x y => hF (by simp only [map_mul, mul_comm])⟩⟩
  let t : N ⋊[integerPowerAction a] Multiplicative ℤ :=
    SemidirectProduct.inr (Multiplicative.ofAdd 1)
  have hconj (x : N) : MulAut.conjNormal t (e x) = e (a x) := by
    apply Subtype.ext
    change t * SemidirectProduct.inl x * t⁻¹ = SemidirectProduct.inl (a x)
    dsimp only [t]
    rw [← map_inv, ← SemidirectProduct.inl_aut]
    change SemidirectProduct.inl ((a ^ (1 : ℤ)) x) = SemidirectProduct.inl (a x)
    rw [zpow_one]
  apply abelian_cyclic_nilpotent_of_unipotent q t (by rfl) F hF T _ hnil
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [hconj]
  change (f (e.symm (e (a y)))).toAdd = T (f (e.symm (e y))).toAdd
  simpa only [e.symm_apply_apply] using hT y

theorem abelian_cyclic_polynomial_growth_virtually_nilpotent
    {G : Type} [Group G] [DecidableEq G]
    [Module.Free ℤ A] [Module.Finite ℤ A]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (f : q.ker ≃* Multiplicative A) : Group.IsVirtuallyNilpotent G := by
  let a : MulAut q.ker := MulAut.conjNormal t
  let T : Module.End ℤ A :=
    ((f.symm.trans (a.trans f)).toAdditive.toIntLinearEquiv).toLinearMap
  have hT (x : q.ker) : (f (a x)).toAdd = T (f x).toAdd := by
    change (f (a x)).toAdd = (f (a (f.symm (f x)))).toAdd
    rw [f.symm_apply_apply]
  obtain ⟨m, hm, hnil⟩ := polynomial_growth_integer_conjugation_unipotent_power
    S hS hgen hvol q.ker t f.toMonoidHom f.surjective T hT
  have hp (n : ℕ) (x : q.ker) : (f ((a ^ n) x)).toAdd = (T ^ n) (f x).toAdd := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, ih, hT, pow_succ, Module.End.mul_apply]
  let : Group.IsNilpotent (q.ker ⋊[integerPowerAction (a ^ m)] Multiplicative ℤ) :=
    semidirect_abelian_nilpotent_of_unipotent (a ^ m) f.toMonoidHom f.injective
      (T ^ m) (hp m) hnil
  let e := cyclicKernelEquiv q t ht
  let j := e.toMonoidHom.comp (cyclicPowerMap a m)
  have hj : Function.Injective j := e.injective.comp (cyclicPowerMap_injective a hm)
  have hji : j.range.FiniteIndex := by
    rw [MonoidHom.range_comp]
    let := cyclicPowerMap_range_finiteIndex a hm
    exact Subgroup.FiniteIndex.map_of_surjective (cyclicPowerMap a m).range e.surjective
  have hnilj : Group.IsNilpotent j.range :=
    Group.nilpotent_of_surjective j.rangeRestrict j.rangeRestrict_surjective
  exact ⟨j.range, hnilj, hji⟩

end PolycyclicRecognition

end

end OAI
