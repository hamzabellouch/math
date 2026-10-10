import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionEnumeration
import OAI.Combinatorics.BalancedRyser.Probability.PermutationHistoryLaw
import OAI.Combinatorics.BalancedRyser.Probability.UniformOrderedSubset
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWitnessPayment

namespace OAI

namespace Balanced.CountingJointLaw

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open UniformDeletionEnumeration CountingExposurePosterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

def deletionArray (ω : Experiment (G := Direction F) (ι := Fin k) (α := F)) :
    Fin (k * (Fintype.card F + 1)) → Line F :=
  fun i => nextLine ω (timeToToken i)

def coverArray (e : Fin m ↪ Line F) (σ : Equiv.Perm (Line F)) : Fin m → Line F :=
  fun i => σ (e i)

def fixedPairMean
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ)
    (D : DeletionSet F k) (C : Finset (Line F)) : ℝ :=
  𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
    𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val)

theorem expect_joint_eq_pairMarkAverage (hk : k ≤ Fintype.card F)
    (e : Fin m ↪ Line F)
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      𝔼 σ : Equiv.Perm (Line F), g (deletionArray ω) (coverArray e σ)) =
      ProfileWitnessPayment.pairMarkAverage k m (fixedPairMean g) := by
  calc
    _ = 𝔼 D : DeletionSet F k,
        𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
          𝔼 σ : Equiv.Perm (Line F),
            g (fun i => (d i).val) (coverArray e σ) :=
      expect_originalExperiment_time hk (fun D d =>
        𝔼 σ : Equiv.Perm (Line F), g (fun i => (d i).val) (coverArray e σ))
    _ = 𝔼 D : DeletionSet F k,
        𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
          𝔼 C ∈ ProfileWitnessPayment.witnesses F m,
            𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val) := by
      apply Finset.expect_congr rfl
      intro D _
      apply Finset.expect_congr rfl
      intro d _
      change (𝔼 σ : Equiv.Perm (Line F), g (fun i => (d i).val) (fun i => σ (e i))) =
        𝔼 C ∈ (Finset.univ : Finset (Line F)).powersetCard m,
          𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val)
      simpa only [Fintype.card_fin] using
        UniformOrderedSubset.expect_permutation_ordered_subset e (g (fun i => (d i).val))
    _ = 𝔼 D : DeletionSet F k,
        𝔼 C ∈ ProfileWitnessPayment.witnesses F m, fixedPairMean g D C := by
      apply Finset.expect_congr rfl
      intro D _
      exact Finset.expect_comm _ _ _
    _ = _ := by
      unfold ProfileWitnessPayment.pairMarkAverage
      simp only [Finset.expect_eq_sum_div_card, Finset.card_univ]
      rw [← Finset.sum_div]
      ring

theorem expect_product_eq_pairMarkAverage (hk : k ≤ Fintype.card F)
    (e : Fin m ↪ Line F)
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F) ×
        Equiv.Perm (Line F), g (deletionArray ω.1) (coverArray e ω.2)) =
      ProfileWitnessPayment.pairMarkAverage k m (fixedPairMean g) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact expect_joint_eq_pairMarkAverage hk e g

theorem fixedPairMean_eq_permutation_average
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ)
    (D : DeletionSet F k) (C : Finset (Line F))
    (d₀ : Fin (k * (Fintype.card F + 1)) ≃ D.val) (c₀ : Fin m ≃ C) :
    fixedPairMean g D C =
      𝔼 p : Equiv.Perm D.val × Equiv.Perm C,
        g (fun i => (p.1 (d₀ i)).val) (fun i => (p.2 (c₀ i)).val) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  unfold fixedPairMean
  symm
  calc
    _ = 𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
        𝔼 p : Equiv.Perm C,
          g (fun i => (d i).val) (fun i => (p (c₀ i)).val) := by
      apply Fintype.expect_equiv (UniformOrderedSubset.enumerationEquiv d₀)
      intro p
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro d _
      apply Fintype.expect_equiv (UniformOrderedSubset.enumerationEquiv c₀)
      intro p
      rfl

theorem probability_eq_pairMarkAverage (hk : k ≤ Fintype.card F)
    (e : Fin m ↪ Line F)
    (P : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → Prop)
    [MeasurableSpace (Experiment (G := Direction F) (ι := Fin k) (α := F) ×
      Equiv.Perm (Line F))]
    [MeasurableSingletonClass (Experiment (G := Direction F) (ι := Fin k) (α := F) ×
      Equiv.Perm (Line F))] :
    letI : Nonempty (Experiment (G := Direction F) (ι := Fin k) (α := F) ×
      Equiv.Perm (Line F)) :=
        ⟨((Equiv.refl _, canonicalOffsets hk), Equiv.refl _)⟩
    (PMF.uniformOfFintype (Experiment (G := Direction F) (ι := Fin k) (α := F) ×
      Equiv.Perm (Line F))).toMeasure.real
        {ω | P (deletionArray ω.1) (coverArray e ω.2)} =
      ProfileWitnessPayment.pairMarkAverage k m
        (fixedPairMean (fun d c => if P d c then (1 : ℝ) else 0)) := by
  let : Nonempty (Experiment (G := Direction F) (ι := Fin k) (α := F) ×
    Equiv.Perm (Line F)) :=
      ⟨((Equiv.refl _, canonicalOffsets hk), Equiv.refl _)⟩
  rw [PermutationHistoryLaw.uniform_measureReal_eq_expect]
  exact expect_product_eq_pairMarkAverage hk e
    (fun d c => if P d c then (1 : ℝ) else 0)

end
end Balanced.CountingJointLaw

end OAI
