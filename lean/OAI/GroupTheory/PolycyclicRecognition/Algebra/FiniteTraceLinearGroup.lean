import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # Finiteness from finitely many traces in a full matrix span

A finite spanning subset of the group supplies trace coordinates. The trace
pairing is nondegenerate, so these coordinates separate group elements.
This is the concrete finite-trace step used in Tits, Section 2.
-/

noncomputable section
namespace PolycyclicRecognition

theorem finite_matrix_group_of_full_span_finite_trace
    {K G I : Type*} [Field K] [Group G] [Fintype I] [DecidableEq I]
    (ρ : G →* Matrix.GeneralLinearGroup I K) (hρ : Function.Injective ρ)
    (hspan : Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤)
    (htrace : (Set.range (fun g => Matrix.trace (ρ g).val)).Finite) : Finite G := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := K) (M := Matrix I I K))
  obtain ⟨T, hT, hST⟩ := Submodule.subset_span_finite_of_subset_span (R := K)
    (show (S : Set (Matrix I I K)) ⊆ Submodule.span K (Set.range (fun g => (ρ g).val)) by
      rw [hspan]
      exact Set.subset_univ _)
  have hTspan : Submodule.span K (T : Set (Matrix I I K)) = ⊤ := by
    apply top_unique
    rw [← hS]
    exact Submodule.span_le.mpr hST
  let Z := Set.range (fun g => Matrix.trace (ρ g).val)
  let : Finite Z := htrace.to_subtype
  have hm (g : G) (B : T) : Matrix.trace ((ρ g).val * B.val) ∈ Z := by
    obtain ⟨h, hh⟩ := hT B.property
    change (ρ h).val = B.val at hh
    refine ⟨g * h, ?_⟩
    change Matrix.trace (ρ (g * h)).val = _
    rw [map_mul]
    change Matrix.trace ((ρ g).val * (ρ h).val) = _
    rw [hh]
  let f : G → (T → Z) := fun g B => ⟨Matrix.trace ((ρ g).val * B.val), hm g B⟩
  apply Finite.of_injective f
  intro g h he
  apply hρ
  apply Units.ext
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  have hB : B ∈ Submodule.span K (T : Set (Matrix I I K)) := by rw [hTspan]; trivial
  induction hB using Submodule.span_induction with
  | mem B hB =>
    exact congrArg Subtype.val (congrFun he ⟨B, hB⟩)
  | zero => simp
  | add B C _ _ hB hC => simp only [Matrix.mul_add, Matrix.trace_add, hB, hC]
  | smul c B _ hB => simp only [Matrix.mul_smul, Matrix.trace_smul, hB]

end PolycyclicRecognition

end

end OAI
