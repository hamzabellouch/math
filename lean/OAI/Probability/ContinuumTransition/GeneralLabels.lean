import OAI.Probability.ContinuumTransition.Assignments

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section GeneralLabels
variable {ι : Type u_1} [Fintype ι]

theorem measurable_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) (β : ℝ) :
    Measurable (fun x : ι → Space => symmetricWeight φ β x) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hm : Measurable (fun x : ι → Space => x ∘ e) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (e i)
  have hh := (measurable_boltzmann hφ β (Fintype.card ι)).comp hm
  change Measurable (fun x => boltzmann φ β (x ∘ e)) at hh
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem symmetricWeight_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (x : ι → Space) :
    symmetricWeight φ β x ≤ Real.exp (β * B * Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := boltzmann_le_of_stable hβ hstable (x ∘ e)
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem integrableOn_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {Ω : Set (ι → Space)} (hΩ : volume Ω ≠ ⊤) :
    IntegrableOn (fun x : ι → Space => symmetricWeight φ β x) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hΩ⟩
  apply (integrable_const (Real.exp (β * B * Fintype.card ι))).mono'
    (measurable_symmetricWeight hφ β).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricWeight_nonneg φ β x)]
  exact symmetricWeight_le_of_stable hβ hstable x

noncomputable def generalPartition (φ : ℝ → ℝ) (β : ℝ) (A : Set Space)
    (ι : Type u_2) [Fintype ι] : ℝ :=
  (∫ x in {x : ι → Space | ∀ i, x i ∈ A}, symmetricWeight φ β x) /
    ((Fintype.card ι).factorial : ℝ)

theorem generalPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    0 ≤ generalPartition φ β A ι := by
  apply div_nonneg
  · apply integral_nonneg
    exact symmetricWeight_nonneg φ β
  · positivity

theorem generalPartition_eq_partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    generalPartition φ β (cube L) (Fin N) = partition φ β L N := by
  classical
  by_cases hN : N = 0
  · subst N
    have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
    have hv : volume.real (Set.univ : Set (Fin 0 → Space)) = 1 := by
      simp [Measure.real, volume_pi]
    simp [generalPartition, partition, symmetricWeight, realPairEnergy, hinj, hv]
  · simp only [generalPartition, partition, hN, ite_false, Fintype.card_fin,
      ← boltzmann_eq_symmetricWeight, div_eq_mul_inv, one_mul]
    ring

theorem volume_generalConfigurations (A : Set Space) :
    volume {x : ι → Space | ∀ i, x i ∈ A} = (volume A) ^ Fintype.card ι := by
  have heq : {x : ι → Space | ∀ i, x i ∈ A} = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp
  rw [heq, volume_pi_pi]
  simp

theorem generalPartition_binary_lower [DecidableEq ι] {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (s : Finset ι) :
    generalPartition φ β A {i : ι // i ∈ s} *
      generalPartition φ β B {i : ι // i ∉ s} ≤ generalPartition φ β C ι := by
  classical
  have hΩ : volume {x : ι → Space | ∀ i, x i ∈ C} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hC
  have hmA : volume A ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono haC)
  have hmB : volume B ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hbC)
  have hΩA : volume {x : {i : ι // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmA
  have hΩB : volume {x : {i : ι // i ∉ s} → Space | ∀ i, x i ∈ B} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmB
  have hInt := integral_lower_separated_product volume hA hB hd s
    (integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (symmetricWeight_relabel φ β)
    (fun t _ x hx i => by
      by_cases hi : i ∈ t
      · exact haC (by simpa only [ite_eq_left hi] using hx i)
      · exact hbC (by simpa only [ite_eq_right hi] using hx i))
    (integrableOn_symmetricWeight hφ hβ hstable hΩA)
    (integrableOn_symmetricWeight hφ hβ hstable hΩB)
    (fun x hx => by
      have hh := symmetricWeight_separated φ hβ (fun i => i ∈ s) hd hcross x
        (fun i hi => by simpa only [ite_eq_left hi] using hx i)
        (fun i hi => by simpa only [ite_eq_right hi] using hx i)
      have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
        Subsingleton.elim _ _
      rw [hfi] at hh
      exact hh)
  have hh := binomial_factorial_cancel (Finset.card_le_univ s) hInt
  simpa only [generalPartition, Fintype.card_subtype_compl,
    Fintype.card_coe, volume_pi] using hh

end GeneralLabels

end ContinuumTemperature
end

end OAI
