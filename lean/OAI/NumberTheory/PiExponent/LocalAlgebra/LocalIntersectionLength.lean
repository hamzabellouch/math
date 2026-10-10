import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor
import OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem finite_length_kernel_eq_cokernel
    (u : M →ₗ[A] M) (hfin : IsFiniteLength A M) :
    Module.length A (LinearMap.ker u) =
      Module.length A (M ⧸ LinearMap.range u) := by
  have hk := Module.length_eq_add_of_exact (LinearMap.ker u).subtype
    (LinearMap.ker u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [u.quotKerEquivRange.length_eq] at hk
  have hr := Module.length_eq_add_of_exact (LinearMap.range u).subtype
    (LinearMap.range u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hfiniteRange : Module.length A (LinearMap.range u) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (hfin.of_injective (Submodule.subtype_injective (LinearMap.range u)))
  apply ENat.add_left_injective_of_ne_top hfiniteRange
  calc
    Module.length A (LinearMap.ker u) + Module.length A (LinearMap.range u) =
        Module.length A M := hk.symm
    _ = Module.length A (M ⧸ LinearMap.range u) +
        Module.length A (LinearMap.range u) := hr.trans (add_comm _ _)

def quotientMul (I : Ideal A) (x : A) : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
  x • LinearMap.id

@[simp] theorem quotientMul_apply (I : Ideal A) (x : A) (y : A ⧸ I) :
    quotientMul I x y = x • y := rfl

@[simp] theorem quotientMul_mk (I : Ideal A) (x a : A) :
    quotientMul I x (I.mkQ a) = I.mkQ (a * x) := by
  change x • I.mkQ a = I.mkQ (a * x)
  calc
    x • I.mkQ a = I.mkQ (x • a) := (I.mkQ.map_smul x a).symm
    _ = I.mkQ (a * x) := by rw [smul_eq_mul, mul_comm]

theorem quotientMul_kernel (I : Ideal A) (x : A) :
    LinearMap.ker (quotientMul I x) = Submodule.map I.mkQ (I.colon {x}) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := I.mkQ_surjective y
    have ha : a * x ∈ I := by
      have hz : quotientMul I x (I.mkQ a) = 0 := hy
      rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    refine ⟨a, ?_, rfl⟩
    change a ∈ I.colon {x}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha
  · rintro ⟨a, ha, rfl⟩
    change a ∈ I.colon {x} at ha
    change quotientMul I x (I.mkQ a) = 0
    rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha

noncomputable def colonQuotientEquivKernel (I : Ideal A) (x : A) :
    ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≃ₗ[A]
      LinearMap.ker (quotientMul I x) :=
  (W22.subquotientEquivImage I (I.colon {x})).trans
    (LinearEquiv.ofEq _ _ (quotientMul_kernel I x).symm)

theorem quotientMul_range (I : Ideal A) (x : A) :
    LinearMap.range (quotientMul I x) = Submodule.map I.mkQ (Ideal.span {x}) := by
  have hcomp : (quotientMul I x).comp I.mkQ =
      I.mkQ.comp (LinearMap.toSpanSingleton A A x) := by
    apply LinearMap.ext
    intro a
    change quotientMul I x (I.mkQ a) = I.mkQ (a * x)
    exact quotientMul_mk I x a
  have hr := congrArg LinearMap.range hcomp
  simpa only [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_toSpanSingleton] using hr

noncomputable def cokernelEquivCut (I : Ideal A) (x : A) :
    ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) ≃ₗ[A]
      A ⧸ (I ⊔ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (quotientMul_range I x)).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {x}))

theorem kernel_length_eq_colon (I : Ideal A) (x : A) :
    Module.length A (LinearMap.ker (quotientMul I x)) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) :=
  (colonQuotientEquivKernel I x).length_eq.symm

theorem cokernel_length_eq_cut (I : Ideal A) (x : A) :
    Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {x})) :=
  (cokernelEquivCut I x).length_eq

theorem finite_length_cut_eq_colon (I : Ideal A) (x : A)
    (hfin : IsFiniteLength A (A ⧸ I)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) := by
  rw [← cokernel_length_eq_cut, ← kernel_length_eq_colon]
  exact (finite_length_kernel_eq_cokernel (quotientMul I x) hfin).symm

theorem regular_colon_length_zero (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) = 0 := by
  rw [← kernel_length_eq_colon, LinearMap.ker_eq_bot.mpr hregular]
  exact Module.length_bot

end PiExponentJets.W28.LocalIntersection

end OAI
