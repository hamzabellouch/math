import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace Problem336.CountableProjective

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

abbrev Prefix (X : Type*) (n : ℕ) := Finset.Iic n → X

def stepEquiv (n : ℕ) : (Prefix X n × X) ≃ᵐ Prefix X (n + 1) :=
  ((MeasurableEquiv.refl (Prefix X n)).prodCongr
    (MeasurableEquiv.piSingleton (X := fun _ => X) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ => X) n.le_succ)

omit [StandardBorelSpace X] [Nonempty X] in
lemma stepEquiv_symm_fst (n : ℕ) (x : Prefix X (n + 1)) :
    ((stepEquiv n).symm x).1 = frestrictLe₂ (π := fun _ => X) n.le_succ x := rfl

variable (P : (n : ℕ) → Measure (Prefix X n)) [probabilityPrefixes : ∀ n, IsProbabilityMeasure (P n)]

def stepLaw (n : ℕ) : Measure (Prefix X n × X) :=
  (P (n + 1)).map (stepEquiv n).symm

instance stepLaw_probability (n : ℕ) : IsProbabilityMeasure (stepLaw P n) := by
  unfold stepLaw
  infer_instance

def transition (n : ℕ) : Kernel (Prefix X n) X :=
  (stepLaw P n).condKernel

instance transition_markov (n : ℕ) : IsMarkovKernel (transition P n) := by
  unfold transition
  infer_instance

variable (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ => X) n.le_succ) = P n)

include hP

omit [StandardBorelSpace X] [Nonempty X] [∀ n, IsProbabilityMeasure (P n)] in
lemma stepLaw_fst (n : ℕ) : (stepLaw P n).fst = P n := by
  rw [Measure.fst, stepLaw, Measure.map_map measurable_fst (stepEquiv n).symm.measurable]
  exact hP n

include probabilityPrefixes in
lemma compProd_transition (n : ℕ) : P n ⊗ₘ transition P n = stepLaw P n := by
  rw [← stepLaw_fst P hP n]
  exact (stepLaw P n).disintegrate (stepLaw P n).condKernel

lemma partialTraj_step (n : ℕ) :
    Kernel.partialTraj (X := fun _ => X) (transition P) n (n + 1) ∘ₘ P n = P (n + 1) := by
  have hg : Measurable (IicProdIoc (X := fun _ => X) n (n + 1)) :=
    measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_self,
    ← Measure.map_comp _ _ hg,
    ← Measure.compProd_eq_comp_prod,
    Measure.compProd_map (MeasurableEquiv.piSingleton (X := fun _ => X) n).measurable,
    compProd_transition P hP n,
    Measure.map_map hg
      (measurable_id.prodMap (MeasurableEquiv.piSingleton (X := fun _ => X) n).measurable)]
  change (stepLaw P n).map (stepEquiv n) = P (n + 1)
  exact (stepEquiv n).map_map_symm

lemma partialTraj_initial (n : ℕ) :
    Kernel.partialTraj (X := fun _ => X) (transition P) 0 n ∘ₘ P 0 = P n := by
  induction n with
  | zero => rw [Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
        ← Measure.comp_assoc, ih, partialTraj_step P hP n]

theorem exists_measure_prefix :
    ∃ μ : Measure (ℕ → X), IsProbabilityMeasure μ ∧
      ∀ n, μ.map (frestrictLe (π := fun _ => X) n) = P n := by
  let μ : Measure (ℕ → X) := Kernel.traj (X := fun _ => X) (transition P) 0 ∘ₘ P 0
  refine ⟨μ, inferInstance, ?_⟩
  intro n
  change (Kernel.traj (X := fun _ => X) (transition P) 0 ∘ₘ P 0).map (frestrictLe n) = P n
  rw [Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe]
  exact partialTraj_initial P hP n

omit hP

theorem exists_projectiveLimit
    (Q : (s : Finset ℕ) → Measure (s → X)) [∀ s, IsProbabilityMeasure (Q s)]
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => X) Q) :
    ∃ μ : Measure (ℕ → X), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ℕ => X) μ Q := by
  obtain ⟨μ, hμ, hmarg⟩ := exists_measure_prefix (fun n => Q (Iic n))
    (fun n => (hQ (Iic (n + 1)) (Iic n) (Iic_subset_Iic.mpr n.le_succ)).symm)
  exact ⟨μ, hμ, (isProjectiveLimit_nat_iff hQ μ).mpr hmarg⟩

end Problem336.CountableProjective

end

end OAI
