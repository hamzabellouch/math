import OAI.Algebra.Finitistic.Dimension.PDTor
import Mathlib.RingTheory.Jacobson.Ideal

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : Type u} [Ring A]

/-- For an Artinian ring the left-defined ring radical annihilates every
actual simple right module. The proof uses cyclicity and a genuine inverse;
it does not assume a left/right-radical identification theorem. -/
theorem right_simple_annihilated [IsArtinianRing A]
    (U : Type u) [AddCommGroup U] [Module Aᵐᵒᵖ U] [IsSimpleModule Aᵐᵒᵖ U]
    (a : A) (ha : a ∈ Ring.jacobson A) (u : U) : MulOpposite.op a • u=0 := by
  by_contra hv
  obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective Aᵐᵒᵖ hv u
  change b • (MulOpposite.op a • u) = u at hb
  have hab : -(a*b.unop) ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson_bot]
    exact (Ring.jacobson A).neg_mem ((Ring.jacobson A).mul_mem_right b.unop ha)
  obtain ⟨z, hz⟩ := Ideal.exists_mul_add_sub_mem_of_mem_jacobson (-(a*b.unop)) hab
  have hz1 : z * (1-a*b.unop)=1 := by
    have h : z * (-(a*b.unop)+1)-1=0 := hz
    simpa [sub_eq_add_neg, add_comm] using sub_eq_zero.mp h
  have hz2 : (1-a*b.unop)*z=1 := mul_eq_one_comm.mp hz1
  have hu : MulOpposite.op (1-a*b.unop) • u=0 := by
    simp [MulOpposite.op_sub, MulOpposite.op_mul, sub_smul, mul_smul, hb]
  have hu0 : u=0 := by
    calc
      u = MulOpposite.op ((1-a*b.unop)*z) • u := by rw [hz2, MulOpposite.op_one, one_smul]
      _ = MulOpposite.op z • (MulOpposite.op (1-a*b.unop) • u) := by
        rw [MulOpposite.op_mul, mul_smul]
      _ = 0 := by rw [hu, smul_zero]
  apply hv
  rw [hu0, smul_zero]

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
  [IsSimpleModule Aᵐᵒᵖ U]
variable (M : PDMinimal.FiniteModule k A)

/-- The derived tensor with every actual simple right module is the tensor
of that simple module with the n-th minimal projective-resolution term. -/
def simpleTorIsoTerm (n : ℕ) : Tor (k := k) U M.cat n ≅
    (tensorFunctor k A U).obj (PDMinimal.term M n).cat := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  exact torIsoTerm U M (right_simple_annihilated U) n
end LittleFinitistic.PDTensor

end

end OAI
