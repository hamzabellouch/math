import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZPipeline

namespace OAI

/-! Full-space error of the literal six-to-four-to-three-to-two-to-XZ compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem bottomDifference_instances {α β : Type}
    (F G : Fintype α) (d e : DecidableEq α)
    (P Q : Fintype β) (a b : DecidableEq β)
    (H : Matrix α α ℂ) (K : Matrix β β ℂ) (r : ℝ)
    (h : |@MediatorGraph.normalizedBottom α F d H -
      @MediatorGraph.normalizedBottom β P a K| ≤ r) :
    |@MediatorGraph.normalizedBottom α G e H -
      @MediatorGraph.normalizedBottom β Q b K| ≤ r := by
  cases Subsingleton.elim F G
  cases Subsingleton.elim d e
  cases Subsingleton.elim P Q
  cases Subsingleton.elim a b
  exact h

def energy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (word xs w)
    (fun p => (coefficient J N p:ℝ)))

def threeEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (threeWord xs w)
    (fun p => (threeCoefficient J N p:ℝ)))

def twoEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (twoWord xs w)
    (fun p => (twoCoefficient J N p:ℝ)))

def xzThreeEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ := by
  letI : Fintype (XZThreeQubit ι κ) := inferInstance
  letI : DecidableEq (XZThreeQubit ι κ) := inferInstance
  exact MediatorGraph.normalizedBottom (qmaPauliFamily (xzThreeWord xs w)
    (fun p => (xzThreeCoefficient J N p:ℝ)))

theorem xzThree_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (xzThreeWord xs w p)) := by
  intro p
  rw [qmaPauliYCount_zero _ (xzThree_noY xs w hlen hx hcover he p)]
  exact ⟨0, rfl⟩

theorem threeEnergy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (N : ℕ) (hN : 1 ≤ N) :
    |threeEnergy xs w J N-MediatorGraph.normalizedBottom
      (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 2/(N:ℝ) :=
  QuantumOrderedTwoStage.accuracy xs w J hx hcover N hN

theorem twoEnergy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |twoEnergy xs w J N-threeEnergy xs w J N| ≤ 1/(N:ℝ) :=
  QuantumOrderedThird.output_accuracy (threeSites xs) (threeWord xs w)
    (threeCoefficient J N) (threeSites_length xs hlen) (threeSites_nodup xs hx)
    (threeSites_cover xs w) (three_even xs w hx hcover he) N hN

theorem xzThreeEnergy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |xzThreeEnergy xs w J N-twoEnergy xs w J N| ≤ 1/(N:ℝ) := by
  simpa only [xzThreeEnergy,twoEnergy,xzThreeWord,xzThreeCoefficient] using
    (QuantumOrderedYY.output_accuracy (twoSites xs w) (twoWord xs w)
      (twoCoefficient J N) (twoSites_length xs w hlen) (twoSites_nodup xs w hlen hx)
      (twoSites_cover xs w) (two_even xs w hlen hx hcover he) N hN)

theorem energy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |energy xs w J N-xzThreeEnergy xs w J N| ≤ 1/(N:ℝ) := by
  have h := QuantumOrderedThird.output_accuracy (xzThreeSites xs w) (xzThreeWord xs w)
      (xzThreeCoefficient J N) (xzThreeSites_length xs w hlen)
      (xzThreeSites_nodup xs w hlen hx) (xzThreeSites_cover xs w hlen hx hcover he)
      (xzThree_even xs w hlen hx hcover he) N hN
  unfold energy xzThreeEnergy word coefficient
  exact bottomDifference_instances _ _ _ _ _ _ _ _ _ _ _ h

theorem accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |energy xs w J N-MediatorGraph.normalizedBottom
      (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 5/(N:ℝ) := by
  let E₀ : ℝ := MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))
  let E₁ : ℝ := threeEnergy xs w J N
  let E₂ : ℝ := twoEnergy xs w J N
  let E₃ : ℝ := xzThreeEnergy xs w J N
  have h₁ : |E₁-E₀| ≤ 2/(N:ℝ) :=
    threeEnergy_error xs w J hx hcover N hN
  have h₂ : |E₂-E₁| ≤ 1/(N:ℝ) :=
    twoEnergy_error xs w J hlen hx hcover he N hN
  have h₃ : |E₃-E₂| ≤ 1/(N:ℝ) :=
    xzThreeEnergy_error xs w J hlen hx hcover he N hN
  have h₄ : |energy xs w J N-E₃| ≤ 1/(N:ℝ) :=
    energy_error xs w J hlen hx hcover he N hN
  calc
    _ ≤ |energy xs w J N-E₃|+|E₃-E₀| := abs_sub_le _ _ _
    _ ≤ |energy xs w J N-E₃|+(|E₃-E₂|+|E₂-E₀|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ |energy xs w J N-E₃|+(|E₃-E₂|+(|E₂-E₁|+|E₁-E₀|)) :=
      add_le_add le_rfl (add_le_add le_rfl (abs_sub_le _ _ _))
    _ ≤ 1/(N:ℝ)+(1/(N:ℝ)+(1/(N:ℝ)+2/(N:ℝ))) :=
      add_le_add h₄ (add_le_add h₃ (add_le_add h₂ h₁))
    _ = 5/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
