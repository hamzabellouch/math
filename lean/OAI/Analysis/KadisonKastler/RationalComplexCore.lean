import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.Bases

namespace OAI

/-! # A countable rational core stable under multiplication by i

All coefficient identities can be made simultaneous on this countable
core before bounded maps are extended to the whole Hilbert space.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The canonical rational scalar action inherited from the complex action. -/
instance (priority := 100) rationalCoreModule : Module ℚ H :=
  Module.compHom H (algebraMap ℚ ℂ)

/-- A dense rational subspace on which all complex-linearity tests remain
countable, since multiplication by `i` preserves the subspace. -/
structure RationalComplexCore where
  space : Submodule ℚ H
  countable : Countable space
  dense : Dense (space : Set H)
  mul_I : ∀ x ∈ space, Complex.I • x ∈ space

/-- Every separable complex normed space admits such a core. -/
theorem exists_rationalComplexCore [SeparableSpace H] : Nonempty (RationalComplexCore H) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let w : Bool × ℕ → H := fun j => if j.1 then Complex.I • v j.2 else v j.2
  let S : Submodule ℚ H := Submodule.span ℚ (Set.range w)
  have hvm (n : ℕ) : v n ∈ S := Submodule.subset_span ⟨(false, n), rfl⟩
  have him (n : ℕ) : Complex.I • v n ∈ S := Submodule.subset_span ⟨(true, n), rfl⟩
  have hI : ∀ x ∈ S, Complex.I • x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨b, n⟩, rfl⟩ := hy
      cases b
      · exact him n
      · have he : Complex.I • (Complex.I • v n) = -(v n) := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change Complex.I • (Complex.I • v n) ∈ S
        rw [he]
        exact S.neg_mem (hvm n)
    | zero => simp only [smul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using S.add_mem hx hy
    | smul r x _ hx => simpa only [smul_comm Complex.I r x] using S.smul_mem r hx
  refine ⟨⟨S, inferInstance, ?_, hI⟩⟩
  exact hv.mono (by rintro _ ⟨n, rfl⟩; exact hvm n)

namespace RationalComplexCore

variable {H} (C : RationalComplexCore H)

/-- Multiplication by i as an endomorphism of the countable core. -/
def mulI : C.space →ₗ[ℚ] C.space where
  toFun x := ⟨Complex.I • (x : H), C.mul_I x x.property⟩
  map_add' x y := Subtype.ext (smul_add Complex.I (x : H) (y : H))
  map_smul' r x := Subtype.ext (smul_comm Complex.I r (x : H))

@[simp]
theorem coe_mulI (x : C.space) : (C.mulI x : H) = Complex.I • (x : H) := rfl

end RationalComplexCore

end

end KadisonKastler

end OAI
