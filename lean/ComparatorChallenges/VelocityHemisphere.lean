import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Direction (d : ℕ) := Fin d × Bool
abbrev Vector (d : ℕ) := Fin d → ℝ
abbrev Row (d : ℕ) := {p : Direction d → ℝ≥0 // ∑ e, p e = 1}
abbrev Environment (d : ℕ) := Lattice d → Row d
abbrev State (d : ℕ) := Environment d × Lattice d
abbrev Path (d : ℕ) := ℕ → Lattice d

def step {d : ℕ} (e : Direction d) : Lattice d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

noncomputable def environmentLaw {d : ℕ} (ν : Measure (Row d)) :
    Measure (Environment d) := Measure.infinitePi (fun _ => ν)

def UniformElliptic {d : ℕ} (ν : Measure (Row d)) : Prop :=
  ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ p ∂ν, ∀ e, κ ≤ p.1 e

lemma measurable_current_row {d : ℕ} :
    Measurable (fun z : State d => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro x
  exact measurable_pi_apply x

noncomputable def transition {d : ℕ} : Kernel (State d) (State d) where
  toFun z := ∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_fun_sum
    intro e _
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp measurable_current_row)).coe_nnreal_ennreal
    · exact (Measure.measurable_coe hs).comp
        (Measure.measurable_dirac.comp (measurable_fst.prodMk
          (measurable_snd.add_const (step e))))

instance transition_markov {d : ℕ} : IsMarkovKernel (transition (d := d)) where
  isProbabilityMeasure z := by
    constructor
    change (∑ e : Direction d,
      ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, (z.1 z.2).2]
    rfl

noncomputable def historyTransition {d : ℕ} (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) where
  toFun z := transition (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := transition.measurable.comp (measurable_pi_apply _)

instance historyTransition_markov {d : ℕ} (n : ℕ) :
    IsMarkovKernel (historyTransition (d := d) n) where
  isProbabilityMeasure _ := transition_markov.isProbabilityMeasure _

noncomputable def initialLaw {d : ℕ} (ν : Measure (Row d)) : Measure (State d) :=
  (environmentLaw ν).map (fun ω => (ω, (0 : Lattice d)))

noncomputable def annealedLaw {d : ℕ} (ν : Measure (Row d)) : Measure (Path d) :=
  (@Kernel.trajMeasure (fun _ => State d) _ (initialLaw ν) (historyTransition (d := d)) _).map
    (fun z n => (z n).2)

def dot {d : ℕ} (v ℓ : Vector d) : ℝ := ∑ i, v i * ℓ i

def realPosition {d : ℕ} (x : Lattice d) : Vector d := fun i => (x i : ℝ)

def TransientPaths {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}

def VelocityPaths {d : ℕ} (v : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n : ℕ => fun i => (X n i:ℝ)/(n:ℝ)) atTop (𝓝 v)}

theorem positive_probability_transience_velocity_hemisphere
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  sorry

end DirectionalTransience

end OAI
