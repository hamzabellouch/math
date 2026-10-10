import Mathlib
import OAI.Probability.LogConcave.Numerics.ChildNoise

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma appendSlots_preserving {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2)
      ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (c+k) => μ) := by
  have hm : Measurable (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right] <;> fun_prop
  refine ⟨hm,?_⟩
  rw [←(Expression.split_slots_preserving μ c k).map_eq,Measure.map_map hm
    (Expression.split_slots_preserving μ c k).measurable]
  have he : (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) ∘
      (fun g : Fin (c+k) → E => ((fun i => g (Fin.castAdd k i)),fun i => g (Fin.natAdd c i)))=id := by
    funext g; exact Fin.append_castAdd_natAdd
  rw [he,Measure.map_id]

lemma finPi_head_preserving {k : ℕ} {E : Fin (k+1) → Type*} [∀i,MeasurableSpace (E i)]
    (μ : ∀i,Measure (E i)) [∀i,SigmaFinite (μ i)] :
    MeasurePreserving (fun z : ∀i,E i => (z 0,fun i : Fin k => z i.succ))
      (Measure.pi μ) ((μ 0).prod (Measure.pi fun i : Fin k => μ i.succ)) := by
  exact measurePreserving_piFinSuccAbove (m:=fun i => inferInstance) μ 0

abbrev RowTape {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) :=
  ∀i,(Fin (C i).slots → Point d) × (Fin (M i).slots → Point d)

def rowLaw {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) : Measure (RowTape C M) :=
  Measure.pi fun i => (Measure.pi fun _ : Fin (C i).slots => stdGaussian (Point d)).prod
    (Measure.pi fun _ : Fin (M i).slots => stdGaussian (Point d))

instance {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) :
    IsProbabilityMeasure (rowLaw C M) := by unfold rowLaw; infer_instance

def concatTerms (D : ℝ) : (k : ℕ) → (a : Fin k → ℝ) → (C : Fin k → Expression X d) →
    (M : Fin k → SeedProgram d) → (E : Expression X d) →
    RowTape C M × (Fin E.slots → Point d) → (Fin (compileTerms D k a C M E).slots → Point d)
  | 0,_,_,_,_,z => z.2
  | k+1,a,C,M,E,z => Fin.append (z.1 0).1 (Fin.append (z.1 0).2
      (concatTerms D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E
        ((fun i => z.1 i.succ),z.2)))

lemma concatTerms_preserving (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    MeasurePreserving (concatTerms D k a C M E)
      ((rowLaw C M).prod (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d)))
      (Measure.pi fun _ : Fin (compileTerms D k a C M E).slots => stdGaussian (Point d)) := by
  induction k with
  | zero =>
    change MeasurePreserving Prod.snd ((rowLaw C M).prod
      (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d))) _
    exact measurePreserving_snd
  | succ k ih =>
    let γ := stdGaussian (Point d)
    let μc := Measure.pi fun _ : Fin (C 0).slots => γ
    let μm := Measure.pi fun _ : Fin (M 0).slots => γ
    let μr := rowLaw (fun i : Fin k => C i.succ) (fun i : Fin k => M i.succ)
    let μe := Measure.pi fun _ : Fin E.slots => γ
    have h₁ := (finPi_head_preserving (fun i =>
      (Measure.pi fun _ : Fin (C i).slots => γ).prod
      (Measure.pi fun _ : Fin (M i).slots => γ))).prod (MeasurePreserving.id μe)
    have h₂ := (measurePreserving_prodAssoc (μc.prod μm) μr μe).comp h₁
    have h₃ := ((MeasurePreserving.id (μc.prod μm)).prod
      (ih (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ))).comp h₂
    have h₄ := (measurePreserving_prodAssoc μc μm
      (Measure.pi fun _ : Fin (compileTerms D k (fun i => a i.succ)
        (fun i => C i.succ) (fun i => M i.succ) E).slots => γ)).comp h₃
    have h₅ := ((MeasurePreserving.id μc).prod (appendSlots_preserving γ _ _)).comp h₄
    exact (appendSlots_preserving γ _ _).comp h₅

lemma leftBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.leftBlock (Fin.append x (Fin.append y z))=x := by
  funext i; exact Fin.append_left _ _ i
lemma middleBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.middleBlock (Fin.append x (Fin.append y z))=y := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.castAdd t i))=y i
  rw [Fin.append_right,Fin.append_left]
lemma rightBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.rightBlock (Fin.append x (Fin.append y z))=z := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.natAdd k i))=z i
  rw [Fin.append_right,Fin.append_right]

lemma eval_concatTerms (V : Point d → ℝ) (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (x : X) (z : RowTape C M × (Fin E.slots → Point d)) :
    (compileTerms D k a C M E).eval V x (concatTerms D k a C M E z)=
      (∑i,a i • (M i).program.run V ((C i).eval V x (z.1 i).1,(M i).damping D (z.1 i).2))+
        E.eval V x z.2 := by
  induction k with
  | zero => simp [compileTerms,concatTerms]
  | succ k ih =>
    simp only [compileTerms,concatTerms,Expression.eval,leftBlock_append,middleBlock_append,
      rightBlock_append,ih,Fin.sum_univ_succ,add_assoc]
end LogConcaveSampling.MeanTree

end

end

end OAI
