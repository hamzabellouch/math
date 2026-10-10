import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHamiltonian
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PublishedInputs

namespace OAI

/-!
# Source spectral bottom and rational normalization

The bottom ranges over every normalized many-spin vector. Uniform
coefficient error controls that variational bottom and the YES/NO
thresholds of the square-lattice Heisenberg problem.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

def allUpSourceBasis (n : ℕ) : SourceSpinBasis n := fun _ => 0

def allUpSourceVector (n : ℕ) : SourceSpinVector n :=
  fun s => if s = allUpSourceBasis n then 1 else 0

theorem allUpSourceVector_mass (n : ℕ) : sourceSpinMass (allUpSourceVector n) = 1 := by
  classical
  simp [sourceSpinMass, allUpSourceVector]

/-- Uniform form bound for the complete signed source Hamiltonian. -/
theorem sourceHamiltonianForm_abs_le (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    |sourceHamiltonianForm d u| ≤
      (3 * ∑ e, |(d.coefficient e : ℝ)|) * sourceSpinMass u := by
  unfold sourceHamiltonianForm
  calc
    |∑ e, (d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u| ≤
        ∑ e, |(d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |(d.coefficient e : ℝ)| * (3 * sourceSpinMass u) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (sourceHeisenbergForm_abs_le (d.left e) (d.right e) u) (abs_nonneg _)
    _ = (3 * ∑ e, |(d.coefficient e : ℝ)|) * sourceSpinMass u := by
      rw [← Finset.sum_mul]
      ring

theorem sourceGroundEnergy_le_trial (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    sourceGroundEnergy d ≤ (sourceHamiltonianForm d u : EReal) :=
  sInf_le ⟨u, hu, rfl⟩

theorem sourceGroundEnergy_lower_of_forall (d : SquareLatticeHeisenberg)
    (a : ℝ)
    (ha : ∀ u : SourceSpinVector d.vertices, sourceSpinMass u = 1 →
      a ≤ sourceHamiltonianForm d u) :
    (a : EReal) ≤ sourceGroundEnergy d := by
  apply le_sInf
  rintro e ⟨u, hu, rfl⟩
  exact EReal.coe_le_coe (ha u hu)

theorem sourceGroundEnergy_lower_bound (d : SquareLatticeHeisenberg) :
    (-(3 * ∑ e, |(d.coefficient e : ℝ)|) : ℝ) ≤ sourceGroundEnergy d := by
  apply sourceGroundEnergy_lower_of_forall
  intro u hu
  have h := (abs_le.mp (sourceHamiltonianForm_abs_le d u)).1
  simpa only [hu, mul_one] using h

theorem sourceGroundEnergy_ne_bot (d : SquareLatticeHeisenberg) :
    sourceGroundEnergy d ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (sourceGroundEnergy_lower_bound d)

theorem sourceGroundEnergy_ne_top (d : SquareLatticeHeisenberg) :
    sourceGroundEnergy d ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (sourceGroundEnergy_le_trial d (allUpSourceVector d.vertices)
      (allUpSourceVector_mass d.vertices))

/-- The finite source bottom, now known to be a real number. -/
def realSourceGroundEnergy (d : SquareLatticeHeisenberg) : ℝ :=
  (sourceGroundEnergy d).toReal

theorem realSourceGroundEnergy_coe (d : SquareLatticeHeisenberg) :
    (realSourceGroundEnergy d : EReal) = sourceGroundEnergy d :=
  EReal.coe_toReal (sourceGroundEnergy_ne_top d) (sourceGroundEnergy_ne_bot d)

theorem realSourceGroundEnergy_le_trial (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    realSourceGroundEnergy d ≤ sourceHamiltonianForm d u := by
  apply EReal.coe_le_coe_iff.mp
  rw [realSourceGroundEnergy_coe]
  exact sourceGroundEnergy_le_trial d u hu

theorem realSourceGroundEnergy_lower_of_forall (d : SquareLatticeHeisenberg)
    (a : ℝ)
    (ha : ∀ u : SourceSpinVector d.vertices, sourceSpinMass u = 1 →
      a ≤ sourceHamiltonianForm d u) :
    a ≤ realSourceGroundEnergy d := by
  apply EReal.coe_le_coe_iff.mp
  rw [realSourceGroundEnergy_coe]
  exact sourceGroundEnergy_lower_of_forall d a ha

def SquareLatticeHeisenberg.withCoefficients (d : SquareLatticeHeisenberg)
    (coefficient : Fin d.edges → ℚ) : SquareLatticeHeisenberg :=
  { d with coefficient := coefficient }

/-- Uniform perturbation of every state controls both variational bottoms. -/
theorem realSourceGroundEnergy_rounding (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) :
    |realSourceGroundEnergy (d.withCoefficients rounded) - realSourceGroundEnergy d| ≤
      3 * ∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)| := by
  let ε : ℝ := 3 * ∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|
  have hpoint (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
      |sourceHamiltonianForm d u - sourceHamiltonianForm (d.withCoefficients rounded) u| ≤
        ε :=
    sourceHamiltonianForm_rounding d (fun e => (rounded e : ℝ)) u hu
  have hl : realSourceGroundEnergy (d.withCoefficients rounded) - ε ≤
      realSourceGroundEnergy d := by
    apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    have h := (abs_le.mp (hpoint u hu)).1
    have htrial := realSourceGroundEnergy_le_trial (d.withCoefficients rounded) u hu
    linarith
  have hu : realSourceGroundEnergy d - ε ≤
      realSourceGroundEnergy (d.withCoefficients rounded) := by
    apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    have h := (abs_le.mp (hpoint u hu)).2
    have htrial := realSourceGroundEnergy_le_trial d u hu
    linarith
  apply abs_le.mpr
  constructor <;> dsimp [ε] at * <;> linarith

/-- The smallest useful energy consequence of coefficient rounding and
scalar-term removal for the source normalization. -/
theorem sourceNormalization_energy_error (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) (c ε : ℝ)
    (hcoeff : (∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|) ≤ ε) :
    |realSourceGroundEnergy (d.withCoefficients rounded) -
      ((realSourceGroundEnergy d + c) - c)| ≤ 3 * ε := by
  have h := realSourceGroundEnergy_rounding d rounded
  simp only [add_sub_cancel_right]
  linarith

/-- Actual spectral-bottom rounding preserves the source YES implication. -/
theorem sourceNormalization_yes (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) {c a aRound cRound ε : ℝ}
    (hcoeff : (∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|) ≤ ε)
    (ha : |aRound - a| ≤ ε) (hc : |cRound - c| ≤ ε)
    (hyes : realSourceGroundEnergy d + c ≤ a) :
    realSourceGroundEnergy (d.withCoefficients rounded) ≤
      normalizedSourceLower aRound cRound ε :=
  normalizedSource_yes (sourceNormalization_energy_error d rounded c ε hcoeff) ha hc hyes

/-- Actual spectral-bottom rounding preserves the source NO implication. -/
theorem sourceNormalization_no (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) {c b bRound cRound ε : ℝ}
    (hcoeff : (∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|) ≤ ε)
    (hb : |bRound - b| ≤ ε) (hc : |cRound - c| ≤ ε)
    (hno : b ≤ realSourceGroundEnergy d + c) :
    normalizedSourceUpper bRound cRound ε ≤
      realSourceGroundEnergy (d.withCoefficients rounded) :=
  normalizedSource_no (sourceNormalization_energy_error d rounded c ε hcoeff) hb hc hno

/-- Source normalization with the papers' error allocation, retaining the
two promise implications and at least `22δ/25` threshold separation. -/
theorem sourceNormalization (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) {c a b aRound bRound cRound δ : ℝ}
    (hgap : δ ≤ b - a)
    (hcoeff : (∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|) ≤ δ / 100)
    (ha : |aRound - a| ≤ δ / 100)
    (hb : |bRound - b| ≤ δ / 100)
    (hc : |cRound - c| ≤ δ / 100) :
    (realSourceGroundEnergy d + c ≤ a →
      realSourceGroundEnergy (d.withCoefficients rounded) ≤
        normalizedSourceLower aRound cRound (δ / 100)) ∧
    (b ≤ realSourceGroundEnergy d + c →
      normalizedSourceUpper bRound cRound (δ / 100) ≤
        realSourceGroundEnergy (d.withCoefficients rounded)) ∧
    22 * δ / 25 ≤ normalizedSourceUpper bRound cRound (δ / 100) -
      normalizedSourceLower aRound cRound (δ / 100) := by
  exact ⟨sourceNormalization_yes d rounded hcoeff ha hc,
    sourceNormalization_no d rounded hcoeff hb hc,
    normalizedSource_gap_fraction hgap ha hb⟩

end ContinuumCoulomb

end

end OAI
