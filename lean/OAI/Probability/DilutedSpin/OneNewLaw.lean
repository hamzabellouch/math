import OAI.Probability.DilutedSpin.CavityRateLimits
import OAI.Probability.DilutedSpin.PerturbedEnergyMean
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

noncomputable def newPotential (theta : X → InteractionSample (q+1))
    (z : X×(Fin q → Fin N)) : (Fin (N+1) → Spin) → ℝ :=
  fun σ => (theta z.1).1 (appendSpin (fun b => σ (z.2 b).succ) (σ 0))

omit [NeZero N] in
lemma measurable_newPotential (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (newPotential (N := N) theta) := by
  apply measurable_from_prod_countable_left
  intro i
  exact Measurable.of_eval (fun σ => by
    change Measurable (fun c => (theta c).1 (appendSpin (fun b => σ (i b).succ) (σ 0)))
    exact hθ _) 

omit [NeZero N] in
lemma spin_insertNth (j : Fin (q+1)) (i : Fin q → Fin N) (σ : Fin (N+1) → Spin) :
    (fun d => σ (j.insertNth (α := fun _ => Fin (N+1)) (0 : Fin (N+1)) (fun b => (i b).succ) d)) =
      j.insertNth (α := fun _ => Spin) (σ 0) (fun b => σ (i b).succ) := by
  funext d
  refine Fin.succAboveCases j ?_ (fun b => ?_) d <;> simp

lemma oneNew_markLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x s => (theta x).1 (fun l => s (e l))) μ μ) :
    Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
        indexedPotential theta (z.1,z.2.1.insertNth (α := fun _ => Fin (N+1)) (0 : Fin (N+1)) (fun i => (z.2.2 i).succ)))
      (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))) =
    Measure.map (newPotential (N := N) theta) (μ.prod (finiteUniform (Fin q → Fin N))) := by
  apply map_redundant_finite_mark μ _ _
  · apply measurable_from_prod_countable_left
    intro b
    exact Measurable.of_eval (fun σ => by
      change Measurable (fun c => (theta c).1 (fun d => σ (b.1.insertNth (α := fun _ => Fin (N+1)) 0 (fun i => (b.2 i).succ) d)))
      exact hθ _)
  · exact measurable_newPotential theta hθ
  · intro j i
    have h := (cavity_coordinate_identDistrib μ (fun x => (theta x).1) hsym j).symm.comp
      (show Measurable (fun e : ((Fin q → Spin) × Spin) → ℝ =>
        fun σ : Fin (N+1) → Spin => e ((fun b => σ (i b).succ),σ 0)) by fun_prop)
    change IdentDistrib
      (fun x (σ : Fin (N+1) → Spin) => (theta x).1
        (fun d => σ (j.insertNth (α := fun _ => Fin (N+1)) 0 (fun b => (i b).succ) d)))
      (fun x (σ : Fin (N+1) → Spin) => (theta x).1 (appendSpin (fun b => σ (i b).succ) (σ 0))) μ μ
    simp only [spin_insertNth]
    exact h

end DilutedSpinGlass

end

end OAI
