import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Function Preorder
open scoped ENNReal
namespace Problem367.CountableProjective

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

private def split (n : ℕ) (x : ∀ i : Iic (n+1), X i) :
    (∀ i : Iic n, X i) × X (n+1) :=
  (frestrictLe₂ (Nat.le_succ n) x, x ⟨n+1, mem_Iic.mpr le_rfl⟩)

private lemma split_measurable (n : ℕ) : Measurable (split (X := X) n) := by
  exact (measurable_frestrictLe₂ _).prodMk (measurable_pi_apply _)

omit [∀ n, MeasurableSpace (X n)] in
private lemma split_injective (n : ℕ) : Injective (split (X := X) n) := by
  intro x y h
  funext i
  by_cases hi : i.val ≤ n
  · exact congrFun (congrArg Prod.fst h) ⟨i.val, mem_Iic.mpr hi⟩
  · have hi' : i.val = n+1 := by have := mem_Iic.mp i.property; omega
    have he : i = ⟨n+1, mem_Iic.mpr le_rfl⟩ := Subtype.ext hi'
    subst i
    exact congrArg Prod.snd h

omit [∀ n, MeasurableSpace (X n)] in
private lemma split_comp_restrict (n : ℕ) :
    split (X := X) n ∘ frestrictLe (n+1) =
      fun x : ∀ n, X n => (frestrictLe n x, x (n+1)) := rfl

variable [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]

theorem exists_nat_marginals
    (μ : (n : ℕ) → Measure (∀ i : Iic n, X i))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, (μ (n+1)).map (frestrictLe₂ (Nat.le_succ n)) = μ n) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (frestrictLe n) = μ n := by
  let κ : (n : ℕ) → Kernel (∀ i : Iic n, X i) (X (n+1)) :=
    fun n => condDistrib (fun x : ∀ i : Iic (n+1), X i =>
      x ⟨n+1, mem_Iic.mpr le_rfl⟩) (frestrictLe₂ (Nat.le_succ n)) (μ (n+1))
  let (n : ℕ) : IsMarkovKernel (κ n) := by dsimp [κ]; infer_instance
  let ν : Measure (∀ n, X n) := (Kernel.traj κ 0) ∘ₘ μ 0
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  refine ⟨ν, hν, ?_⟩
  have hstep (n : ℕ) :
      (ν.map (frestrictLe n)) ⊗ₘ κ n =
        ν.map (fun x => (frestrictLe n x, x (n+1))) := by
    rw [Measure.compProd_eq_comp_prod]
    dsimp [ν]
    rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
      Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
    congr with x₀ : 1
    rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
      Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)]
  intro n
  induction n with
  | zero =>
    dsimp [ν]
    rw [Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
    apply (split_measurable (X := X) n).measurableEmbedding (split_injective n) |>.map_injective
    rw [Measure.map_map (split_measurable n) (measurable_frestrictLe _)]
    rw [split_comp_restrict, ← hstep, ih]
    have hc := compProd_map_condDistrib (mβ := inferInstance)
      (μ := μ (n+1)) (X := frestrictLe₂ (Nat.le_succ n))
      (Y := fun x : ∀ i : Iic (n+1), X i => x ⟨n+1, mem_Iic.mpr le_rfl⟩)
      (measurable_frestrictLe₂ _).aemeasurable
      (measurable_pi_apply _).aemeasurable
    rw [hμ n] at hc
    exact hc

theorem exists_nat_projective_limit
    (μ : (I : Finset ℕ) → Measure (∀ i : I, X i))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily μ) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧ IsProjectiveLimit ν μ := by
  obtain ⟨ν, hν, hmarg⟩ := exists_nat_marginals (fun n => μ (Iic n))
    (fun n => (hμ (Iic (n+1)) (Iic n) (Iic_subset_Iic.mpr (Nat.le_succ n))).symm)
  exact ⟨ν, hν, (isProjectiveLimit_nat_iff hμ ν).mpr hmarg⟩

end Problem367.CountableProjective

end

end OAI
