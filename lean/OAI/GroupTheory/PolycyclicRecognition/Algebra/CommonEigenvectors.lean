import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Minimal
import Mathlib.RingTheory.Artinian.Module

namespace OAI

/-! # Finite common eigenspaces and a common eigenvector

Common eigenspaces form an independent family even when the operators do
not commute. For commuting operators over an algebraically closed field,
a minimal nonzero invariant subspace supplies a common eigenvector.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def commonEigenspace (f : I → Module.End K V) (χ : I → K) : Submodule K V :=
  ⨅ i, (f i).eigenspace (χ i)

theorem mem_commonEigenspace (f : I → Module.End K V) (χ : I → K) (v : V) :
    v ∈ commonEigenspace f χ ↔ ∀ i, f i v = χ i • v := by
  simp only [commonEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem commonEigenspace_independent (f : I → Module.End K V) :
    iSupIndep (commonEigenspace f) :=
  iSupIndep.iInf (fun i μ => (f i).eigenspace μ) (fun i => (f i).eigenspaces_iSupIndep)

theorem finite_commonEigenspaces [Module.Finite K V] (f : I → Module.End K V) :
    {χ : I → K | commonEigenspace f χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (commonEigenspace_independent f)

theorem exists_commonEigenspace [Module.Finite K V] [Nontrivial V] [IsAlgClosed K]
    (f : I → Module.End K V) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ χ : I → K, commonEigenspace f χ ≠ ⊥ := by
  let P (W : Submodule K V) := W ≠ ⊥ ∧ ∀ i, Set.MapsTo (f i) W W
  obtain ⟨W, hW⟩ := exists_minimal_of_wellFoundedLT P
    ⟨⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  have hWnonzero := hW.prop.1
  have hWinv := hW.prop.2
  let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hWnonzero
  have hs (i : I) : ∃ μ : K, ∀ w : W, f i w = μ • (w : V) := by
    let r := (f i).restrict (hWinv i)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue r
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    have hvEigen : f i (v : V) = μ • (v : V) := by
      exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)
    let U := W ⊓ (f i).eigenspace μ
    have hUnonzero : U ≠ ⊥ := by
      intro heq
      have hh : (v : V) ∈ U := ⟨v.property, Module.End.mem_eigenspace_iff.mpr hvEigen⟩
      rw [heq, Submodule.mem_bot] at hh
      exact hv0 (Subtype.ext hh)
    have hUinv (j : I) : Set.MapsTo (f j) U U := by
      intro x hx
      refine ⟨hWinv j hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
      have hxEigen := Module.End.mem_eigenspace_iff.mp hx.2
      calc
        f i (f j x) = f j (f i x) := congrArg (fun a : Module.End K V => a x) (hcomm i j).eq
        _ = μ • f j x := by rw [hxEigen, map_smul]
    have hWU : W ≤ U := hW.le_of_le ⟨hUnonzero, hUinv⟩ inf_le_left
    exact ⟨μ, fun w => Module.End.mem_eigenspace_iff.mp (hWU w.property).2⟩
  choose χ hχ using hs
  refine ⟨χ, ?_⟩
  intro heq
  apply hWnonzero
  apply eq_bot_iff.mpr
  intro v hv
  have hh : v ∈ commonEigenspace f χ := (mem_commonEigenspace f χ v).mpr
    (fun i => hχ i ⟨v, hv⟩)
  simpa only [heq] using hh

end PolycyclicRecognition

end

end OAI
