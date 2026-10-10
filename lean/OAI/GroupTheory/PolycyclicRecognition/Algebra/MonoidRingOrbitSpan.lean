import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.NatInt

namespace OAI

/-! # Finite module generators and integral spans of monoid orbits -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M : Type} [Monoid Q] [AddCommGroup M] [Module ℤ[Q] M]

def monoidOrbitSet (s : Set M) : Set M :=
  {x | ∃ q : Q, ∃ y ∈ s, MonoidAlgebra.of ℤ Q q • y = x}

theorem monoidOrbitSpan_stable (s : Set M) (q : Q) (x : M)
    (hx : x ∈ Submodule.span ℤ (monoidOrbitSet (Q := Q) s)) :
    MonoidAlgebra.of ℤ Q q • x ∈ Submodule.span ℤ (monoidOrbitSet (Q := Q) s) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨q * r, z, hz, ?_⟩
    rw [map_mul, mul_smul]
  | zero => simpa only [smul_zero] using (Submodule.span ℤ (monoidOrbitSet (Q := Q) s)).zero_mem
  | add x y _ _ hx hy => simpa only [smul_add] using
      (Submodule.span ℤ (monoidOrbitSet (Q := Q) s)).add_mem hx hy
  | smul r x _ hx =>
    rw [smul_comm]
    exact (Submodule.span ℤ (monoidOrbitSet (Q := Q) s)).smul_mem r hx

theorem monoidOrbitSpan_eq_top (s : Set M) (hs : Submodule.span ℤ[Q] s = ⊤) :
    Submodule.span ℤ (monoidOrbitSet (Q := Q) s) = ⊤ := by
  let W := Submodule.span ℤ (monoidOrbitSet (Q := Q) s)
  let U : Submodule ℤ[Q] M := MonoidAlgebra.submoduleOfSMulMem W (monoidOrbitSpan_stable s)
  have hU : Submodule.span ℤ[Q] s ≤ U := by
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.subset_span
    refine ⟨1, x, hx, ?_⟩
    rw [map_one, one_smul]
  apply top_unique
  intro x _
  change x ∈ U
  apply hU
  rw [hs]
  trivial

theorem exists_finite_monoidOrbitSpan [Module.Finite ℤ[Q] M] :
    ∃ s : Finset M, Submodule.span ℤ (monoidOrbitSet (Q := Q) (s : Set M)) = ⊤ := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ[Q] M).FG)
  exact ⟨s, monoidOrbitSpan_eq_top (s : Set M) hs⟩

theorem finite_of_monoidOrbitSpan (s : Finset M)
    (hs : Submodule.span ℤ (monoidOrbitSet (Q := Q) (s : Set M)) = ⊤) :
    Module.Finite ℤ[Q] M := by
  let U := Submodule.span ℤ[Q] (s : Set M)
  have hle : Submodule.span ℤ (monoidOrbitSet (Q := Q) (s : Set M)) ≤
      U.restrictScalars ℤ := by
    apply Submodule.span_le.mpr
    rintro x ⟨q, y, hy, rfl⟩
    exact U.smul_mem _ (Submodule.subset_span hy)
  have hU : U = ⊤ := by
    apply top_unique
    intro x _
    exact hle (hs ▸ Submodule.mem_top)
  exact Module.Finite.of_fg_top ⟨s, hU⟩

end PolycyclicRecognition

end

end OAI
