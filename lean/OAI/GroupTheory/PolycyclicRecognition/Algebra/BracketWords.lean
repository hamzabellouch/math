import Mathlib.Algebra.Free
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Actual bracket words for the nilpotent box construction

The linear span of evaluated bracket words is exactly the generated Lie
subalgebra. A finite-dimensional generated algebra therefore has a basis
chosen from actual words. Letter counts give the weights of these words,
including for generalized weight vectors.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators
open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

def evalBracketWord (X : I → L) : FreeMagma I → L
  | .of i => X i
  | .mul a b => ⁅evalBracketWord X a, evalBracketWord X b⁆

omit [LieAlgebra ℝ L] in
@[simp] theorem evalBracketWord_of (X : I → L) (i : I) :
    evalBracketWord X (.of i) = X i := rfl

omit [LieAlgebra ℝ L] in
@[simp] theorem evalBracketWord_mul (X : I → L) (a b : FreeMagma I) :
    evalBracketWord X (a * b) = ⁅evalBracketWord X a, evalBracketWord X b⁆ := rfl

def bracketWordCount [DecidableEq I] : FreeMagma I → I → ℕ
  | .of j, i => if i = j then 1 else 0
  | .mul a b, i => bracketWordCount a i + bracketWordCount b i

theorem evalBracketWord_mem_lieSpan (X : I → L) (w : FreeMagma I) :
    evalBracketWord X w ∈ LieSubalgebra.lieSpan ℝ L (Set.range X) := by
  induction w using FreeMagma.rec with
  | of i => exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
  | mul a b ha hb => exact LieSubalgebra.lie_mem _ ha hb

theorem evalBracketWord_map {L' : Type*} [LieRing L'] [LieAlgebra ℝ L']
    (f : L →ₗ⁅ℝ⁆ L') (X : I → L) (w : FreeMagma I) :
    f (evalBracketWord X w) = evalBracketWord (fun i => f (X i)) w := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => simp only [evalBracketWord, f.map_lie, ha, hb]

theorem span_evalBracketWord (X : I → L) :
    Submodule.span ℝ (Set.range (evalBracketWord X)) =
      (LieSubalgebra.lieSpan ℝ L (Set.range X)).toSubmodule := by
  let S := Submodule.span ℝ (Set.range (evalBracketWord X))
  have hbracket : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, rfl⟩ := hy
        exact Submodule.subset_span ⟨a * b, rfl⟩
      | zero => simpa only [lie_zero] using S.zero_mem
      | add y z _ _ hy hz => simpa only [lie_add] using S.add_mem hy hz
      | smul r y _ hy => simpa only [lie_smul] using S.smul_mem r hy
    | zero => intro y _; simpa only [zero_lie] using S.zero_mem
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [add_lie] using S.add_mem (hx y hy) (hz y hy)
    | smul r x _ hx =>
      intro y hy
      simpa only [smul_lie] using S.smul_mem r (hx y hy)
  let K : LieSubalgebra ℝ L := { S with lie_mem' := fun hx hy => hbracket _ hx _ hy }
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro _ ⟨w, rfl⟩
      exact evalBracketWord_mem_lieSpan X w)
  · change LieSubalgebra.lieSpan ℝ L (Set.range X) ≤ K
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨.of i, rfl⟩

/-- No abstract choice of a spanning vector is needed: every selected basis
vector is the evaluation of a bracket word in the supplied generators. -/
theorem exists_bracketWord_basis [FiniteDimensional ℝ L] (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ L)) ℝ L,
      ∀ k, ∃ w : FreeMagma I, evalBracketWord X w = b k := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range (evalBracketWord X)) := by
    rw [span_evalBracketWord, hX]
    rfl
  let J := (linearIndepOn_empty ℝ (id : L → L)).extend
    (Set.empty_subset (Set.range (evalBracketWord X)))
  let b : Basis J ℝ L := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (Module.finrank ℝ L) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, fun k => ?_⟩
  simpa only [Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
    (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ Set.range b from ⟨_, rfl⟩))

def bracketWordWeight {H : Type*} [AddCommGroup H] [Module ℝ H]
    (α : I → H →ₗ[ℝ] ℝ) : FreeMagma I → H →ₗ[ℝ] ℝ
  | .of i => α i
  | .mul a b => bracketWordWeight α a + bracketWordWeight α b

theorem bracketWordWeight_eq_count [Fintype I] [DecidableEq I]
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (α : I → H →ₗ[ℝ] ℝ) (w : FreeMagma I) (h : H) :
    bracketWordWeight α w h = ∑ i, (bracketWordCount w i : ℝ) * α i h := by
  induction w using FreeMagma.rec with
  | of j => simp [bracketWordWeight, bracketWordCount]
  | mul a b ha hb =>
    simp only [bracketWordWeight, LinearMap.add_apply, ha, hb,
      bracketWordCount, Nat.cast_add, add_mul, Finset.sum_add_distrib]

/-- Generalized weight vectors remain generalized after taking brackets.
The nilpotent part of the Cartan action is retained. -/
theorem evalBracketWord_mem_generalizedWeight
    (H : LieSubalgebra ℝ L) (α : I → H →ₗ[ℝ] ℝ) (X : I → L)
    (hX : ∀ i (h : H), X i ∈ (LieAlgebra.ad ℝ L h).maxGenEigenspace (α i h))
    (w : FreeMagma I) (h : H) :
    evalBracketWord X w ∈
      (LieAlgebra.ad ℝ L h).maxGenEigenspace (bracketWordWeight α w h) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i h
  | mul a b ha hb =>
    exact LieModule.lie_mem_maxGenEigenspace_toEnd ha hb

end PolycyclicRecognition

end

end OAI
