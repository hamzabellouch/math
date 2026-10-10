import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelPipeline

namespace OAI

/-! Each literal list stage is exactly the corresponding ordered Pauli
construction, with explicit finite product and sum enumerations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open QuantumOrderedLabelData QuantumOrderedLabelFamily
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n d : ℕ}

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem value_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ)
    (ys : κ × Fin d → List (ι ⊕ κ)) (v : κ × Fin d → ι ⊕ κ → Fin 4)
    (h : ∀ p, tag (Sum.elim (index q) (fun a => n+(e.symm a).val)) (ys p) (v p) =
      f (n+(e.symm p.1).val) (tag (index q) (xs p.1) (w p.1)) p.2) :
    value d f g (N,n,table e (index q) xs w J) =
      (n+m,table (nextTerm e d) (index (nextQubit q e)) ys v
        (fun p => g (QuantumOrderedSubdivision.scale J N) (J p.1) p.2)) := by
  apply Prod.ext
  · simp only [value,table,List.length_ofFn]
  · rw [show (value d f g (N,n,table e (index q) xs w J)).2 =
        family d f g (N,n,table e (index q) xs w J) from rfl,
      family_table]
    unfold table
    apply congrArg List.ofFn
    funext i
    dsimp only
    rw [nextQubit_index,h]

theorem subdivision_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ a, (xs a).Nodup) (N cut : ℕ) :
    QuantumOrderedLabelPipeline.subdivisionStep cut (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedSubdivision.outputSites xs cut)
        (QuantumOrderedSubdivision.outputWord xs cut w)
        (QuantumOrderedSubdivision.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (subdivision_tag (index q) (fun a => n+(e.symm a).val) xs w hx cut)

theorem third_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 3) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.thirdStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 7) (index (nextQubit q e))
        (QuantumOrderedThird.outputSites xs w) (QuantumOrderedThird.outputWord xs w)
        (QuantumOrderedThird.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (thirdBlock_tag (index q) (fun a => n+(e.symm a).val) xs w hlen hx)

omit [Fintype ι] in
theorem yy_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.yyStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedYY.outputSites xs) (QuantumOrderedYY.outputWord xs w)
        (QuantumOrderedYY.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (yyBlock_tag (index q) (fun a => n+(e.symm a).val) xs w hx)

omit [Fintype ι] in
theorem private_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) :
    QuantumOrderedLabelPipeline.privateStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedPrivate.outputSites xs) (QuantumOrderedPrivate.outputWord xs w)
        (QuantumOrderedPrivate.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (privateBlock_tag (index q) (fun a => n+(e.symm a).val) xs w)

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
