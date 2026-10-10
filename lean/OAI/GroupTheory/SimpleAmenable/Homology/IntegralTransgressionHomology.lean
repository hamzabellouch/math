import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.VerticalStringResolution

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralTransgressionHomology
open Classical
open scoped TensorProduct
namespace IntegralTransgression
open groupHomology
variable {H E : Type} [Group H] [Group E]

abbrev coefficients (E : Type) [Group E] := Rep.trivial ℤ E ℤ

theorem d2_surjective [Group.IsPerfect E] :
    Function.Surjective (d₂₁ (coefficients E)) := by
  intro z
  let c : cycles₁ (coefficients E) := (cycles₁IsoOfIsTrivial (coefficients E)).inv z
  have hz : H1π (coefficients E) c = 0 := by
    apply (H1AddEquivOfIsTrivial (coefficients E)).injective
    have : Group.IsPerfect (Abelianization E) :=
      Group.IsPerfect.ofSurjective (f := Abelianization.of) (QuotientGroup.mk'_surjective (commutator E))
    have : Subsingleton (Abelianization E) := inferInstance
    have : Subsingleton (Additive (Abelianization E) ⊗[ℤ] ℤ) := inferInstance
    exact Subsingleton.elim _ _
  have h := (H1π_eq_zero_iff c).mp hz
  exact h

variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

noncomputable def onChains : (E × E →₀ ℤ) →ₗ[ℤ] Additive (Kernel q hc) :=
  Finsupp.linearCombination ℤ (fun xy : E×E => Additive.ofMul (factor q hq hc xy.1 xy.2))

@[simp] theorem onChains_single (x y : E) (n : ℤ) :
    onChains q hq hc (Finsupp.single (x,y) n)= n • Additive.ofMul (factor q hq hc x y) := by
  simp only [onChains,Finsupp.linearCombination_single]

theorem additive_cocycle (x y z : E) :
    Additive.ofMul (factor q hq hc y z) - Additive.ofMul (factor q hq hc (x*y) z) +
      Additive.ofMul (factor q hq hc x (y*z)) - Additive.ofMul (factor q hq hc x y)=0 := by
  have he : Additive.ofMul (factor q hq hc x y) + Additive.ofMul (factor q hq hc (x*y) z) =
      Additive.ofMul (factor q hq hc y z) + Additive.ofMul (factor q hq hc x (y*z)) :=
    congrArg Additive.ofMul (factor_cocycle q hq hc x y z)
  calc
    _ = (Additive.ofMul (factor q hq hc y z) + Additive.ofMul (factor q hq hc x (y*z))) -
        (Additive.ofMul (factor q hq hc x y) + Additive.ofMul (factor q hq hc (x*y) z)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

theorem onChains_d3 :
    (onChains q hq hc).comp (d₃₂ (coefficients E)).hom = 0 := by
  apply Finsupp.lhom_ext
  intro xyz n
  rcases xyz with ⟨x,y,z⟩
  change onChains q hq hc (d₃₂ (coefficients E) (Finsupp.single (x,y,z) n)) = 0
  rw [d₃₂_single (A := coefficients E) (x,y,z) n]
  change onChains q hq hc ((Finsupp.single (y,z) n - Finsupp.single (x*y,z) n) +
    Finsupp.single (x,y*z) n - Finsupp.single (x,y) n)=0
  rw [(onChains q hq hc).map_sub, (onChains q hq hc).map_add,
    (onChains q hq hc).map_sub]
  simp only [onChains_single]
  simpa only [zsmul_sub,zsmul_add,zsmul_zero] using
    congrArg (fun v : Additive (Kernel q hc) => (n : ℤ) • v) (additive_cocycle q hq hc x y z)

noncomputable def onCycles : cycles₂ (coefficients E) →ₗ[ℤ] Additive (Kernel q hc) :=
  (onChains q hq hc).comp (cycles₂ (coefficients E)).subtype

end IntegralTransgression
end IntegralTransgressionHomology

section IntegralTransgressionSurjective
open Classical
namespace IntegralTransgression
open groupHomology

noncomputable def factorThrough {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : M →ₗ[R] P) (hg : f.ker ≤ g.ker) : N →ₗ[R] P :=
  (f.ker.liftQ g hg).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

@[simp] theorem factorThrough_apply {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : M →ₗ[R] P) (hg : f.ker ≤ g.ker) (x : M) :
    factorThrough f hf g hg (f x)=g x := by
  simp [factorThrough]

variable {H E : Type} [Group H] [Group E]
variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

theorem onCycles_surjective [Group.IsPerfect H] :
    Function.Surjective (onCycles q hq hc) := by
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := q) hq
  let R := (onCycles q hq hc).range
  let Q := Additive (Kernel q hc) ⧸ R
  let u : (E×E →₀ ℤ) →ₗ[ℤ] Q := R.mkQ.comp (onChains q hq hc)
  have hu : (d₂₁ (coefficients E)).hom.ker ≤ u.ker := by
    intro x hx
    change R.mkQ (onChains q hq hc x)=0
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    exact ⟨⟨x,hx⟩,rfl⟩
  let b : (E →₀ ℤ) →ₗ[ℤ] Q :=
    factorThrough (d₂₁ (coefficients E)).hom d2_surjective u hu
  have hb (x : E×E →₀ ℤ) : b (d₂₁ (coefficients E) x)=u x :=
    factorThrough_apply _ _ _ _ x
  have hp (x y : E) :
      R.mkQ (Additive.ofMul (factor q hq hc x y)) =
        b (Finsupp.single y 1) - b (Finsupp.single (x*y) 1) + b (Finsupp.single x 1) := by
    have ht := hb (Finsupp.single (x,y) 1)
    change b (d₂₁ (coefficients E) (Finsupp.single (x,y) (1:ℤ))) =
      R.mkQ (onChains q hq hc (Finsupp.single (x,y) 1)) at ht
    rw [d₂₁_single (A:=coefficients E) (x,y) (1:ℤ)] at ht
    change b (Finsupp.single y 1 - Finsupp.single (x*y) 1 + Finsupp.single x 1) =
      R.mkQ (onChains q hq hc (Finsupp.single (x,y) 1)) at ht
    simpa only [map_add,map_sub,onChains_single,one_smul] using ht.symm
  have hb1 : b (Finsupp.single 1 1)=0 := by
    simpa using (hp 1 1).symm
  let t : H →* Multiplicative Q :=
    { toFun := fun h => Multiplicative.ofAdd
        (R.mkQ (Additive.ofMul (remainder q hq hc h)) + b (Finsupp.single (q h) 1))
      map_one' := by
        apply Multiplicative.toAdd.injective
        change R.mkQ (Additive.ofMul (remainder q hq hc 1)) + b (Finsupp.single (q 1) 1)=0
        simp [hb1]
      map_mul' h k := by
        apply Multiplicative.toAdd.injective
        change R.mkQ (Additive.ofMul (remainder q hq hc (h*k))) +
            b (Finsupp.single (q (h*k)) 1) =
          (R.mkQ (Additive.ofMul (remainder q hq hc h)) + b (Finsupp.single (q h) 1)) +
          (R.mkQ (Additive.ofMul (remainder q hq hc k)) + b (Finsupp.single (q k) 1))
        rw [remainder_mul]
        change R.mkQ (Additive.ofMul (remainder q hq hc h) +
            Additive.ofMul (remainder q hq hc k) + Additive.ofMul (factor q hq hc (q h) (q k))) +
            b (Finsupp.single (q (h*k)) 1) = _
        rw [map_add,map_add,hp,map_mul]
        abel }
  have ht (h : H) : t h=1 := by
    let : Group.IsPerfect t.range := Group.IsPerfect.range t
    have : Subsingleton t.range := inferInstance
    exact congrArg Subtype.val (Subsingleton.elim (⟨t h,h,rfl⟩ : t.range) 1)
  intro k
  have hz : R.mkQ k=0 := by
    have he := congrArg Multiplicative.toAdd (ht (inclusion q hc k.toMul))
    change R.mkQ (Additive.ofMul (remainder q hq hc (inclusion q hc k.toMul))) +
      b (Finsupp.single (q (inclusion q hc k.toMul)) 1)=0 at he
    have hk : q (inclusion q hc k.toMul)=1 := k.toMul.property
    simpa only [remainder_inclusion,ofMul_toMul,hk,hb1,add_zero] using he
  exact (Submodule.Quotient.mk_eq_zero R).mp hz

end IntegralTransgression
end IntegralTransgressionSurjective

end SimpleAmenable
end
end

end OAI
