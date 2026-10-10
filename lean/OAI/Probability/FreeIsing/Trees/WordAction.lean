import OAI.Probability.FreeIsing.Estimates.RadialRepresentation
import OAI.Probability.FreeIsing.Trees.Koopman

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

def wordAut {d : ℕ} : List (Fin d) → TreeAut d
  | [] => TreeAut.refl d
  | c :: w => (wordAut w).trans (prefixTreeAut c)

theorem wordAut_root {d : ℕ} (w : List (Fin d))
    (hw : w.IsChain (· ≠ ·)) :
    (wordAut w).toEquiv ⟨[], List.IsChain.nil⟩ = ⟨w, hw⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change prefixFlip c ((wordAut w).toEquiv ⟨[], List.IsChain.nil⟩) = _
    rw [ih hw.tail]
    apply Subtype.ext
    cases w with
    | nil => rfl
    | cons a w =>
      simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp hw).1]

def wordRelabel {d : ℕ} (w : List (Fin d)) :
    (TreeVertex d → ℝ) → (TreeVertex d → ℝ) :=
  relabel (wordAut w).symm

theorem wordRelabel_measurePreserving {d : ℕ} (w : List (Fin d)) :
    MeasurePreserving (wordRelabel w) (labelMeasure d) (labelMeasure d) :=
  measurePreserving_relabel (wordAut w).symm

@[simp] theorem wordRelabel_nil {d : ℕ} : wordRelabel ([] : List (Fin d)) = id := rfl

@[simp] theorem wordRelabel_cons {d : ℕ} (c : Fin d) (w : List (Fin d)) :
    wordRelabel (c :: w) = wordRelabel w ∘ reflection c := rfl

def generatorOperator {d : ℕ} (c : Fin d) :
    Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) :=
  koopmanL2 (reflection c) (reflection_measurePreserving c)

@[simp] theorem generatorOperator_sq {d : ℕ} (c : Fin d) :
    generatorOperator c * generatorOperator c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact koopmanL2_involutive _ _ (reflection_involutive c) f

theorem list_koopman_eq {d : ℕ} (w : List (Fin d)) :
    (w.map generatorOperator).prod =
      koopmanL2 (wordRelabel w) (wordRelabel_measurePreserving w) := by
  induction w with
  | nil =>
    apply ContinuousLinearMap.ext
    intro f
    change f = Lp.compMeasurePreserving id _ f
    simp
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving (reflection c) _
      (Lp.compMeasurePreserving (wordRelabel w) _ f) =
      Lp.compMeasurePreserving (wordRelabel (c :: w)) _ f
    exact (Lp.compMeasurePreserving_comp_apply f
      (wordRelabel_measurePreserving w) (reflection_measurePreserving c)).symm

theorem wordOperator_eq {d : ℕ} (v : TreeVertex d) :
    RadialWalk.wordOperator generatorOperator v =
      koopmanL2 (wordRelabel v.1) (wordRelabel_measurePreserving v.1) :=
  list_koopman_eq v.1

@[simp] theorem wordOperator_norm {d : ℕ} (v : TreeVertex d)
    (f : Lp ℝ 2 (labelMeasure d)) :
    ‖RadialWalk.wordOperator generatorOperator v f‖ = ‖f‖ := by
  rw [wordOperator_eq, koopmanL2_norm]

theorem operatorAverage_eq {d : ℕ} :
    RadialWalk.operatorAverage (generatorOperator (d := d)) = average d := by
  simp [RadialWalk.operatorAverage, average, koopmanAverage, generatorOperator]

theorem wordOperator_toLp_root {d : ℕ}
    (Z : (TreeVertex d → ℝ) → (TreeVertex d → ℝ))
    (hZ : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Z (relabel g U) = relabel g (Z U))
    (hLp : ∀ v, MemLp (fun U => Z U v) 2 (labelMeasure d))
    (v : TreeVertex d) :
    RadialWalk.wordOperator generatorOperator v
      ((hLp ⟨[], List.IsChain.nil⟩).toLp (fun U => Z U ⟨[], List.IsChain.nil⟩)) =
      (hLp v).toLp (fun U => Z U v) := by
  rw [wordOperator_eq]
  change Lp.compMeasurePreserving (wordRelabel v.1) _
    ((hLp ⟨[], List.IsChain.nil⟩).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  filter_upwards [hZ (wordAut v.1).symm] with U hU
  have h := congrFun hU ⟨[], List.IsChain.nil⟩
  change Z (wordRelabel v.1 U) ⟨[], List.IsChain.nil⟩ =
    Z U ((wordAut v.1).toEquiv ⟨[], List.IsChain.nil⟩) at h
  simpa only [Function.comp_apply, wordAut_root v.1 v.2] using h

end Problem367.TreeKoopman

end

end OAI
