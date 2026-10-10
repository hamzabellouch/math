import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionLimit
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarkedError
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMarks

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Balanced.ProfileFiniteMarks

open ConditionalOrderVariance ProfileMarkedOrders ProfileScheduledMarks
open ProfileDetectionBridge ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def detectionSum (U : Finset (Line F)) (z : U → ℝ)
    (a b : U → U → ℝ) (η ε : ℝ) : ℝ :=
  ∑ i : U, 𝔼 x : U,
    if η < z i ∧ z i < 1 ∧ 3 * ε < |a i x - b i x| then (1 : ℝ) else 0

omit [Field F] [Fintype F] [DecidableEq F] in
theorem detectionSum_le_cutoffSum (U : Finset (Line F)) (z : U → ℝ)
    (a b : U → U → ℝ) (η ε : ℝ) :
    detectionSum U z a b η ε ≤ ∑ i : U, if η < z i then
      (𝔼 x : U, if 3 * ε < |a i x - b i x| then (1 : ℝ) else 0) else 0 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : η < z i
  · simp only [ite_eq_left hi]
    apply Finset.expect_le_expect
    intro x _
    split_ifs <;> simp_all
  · simp [hi]

theorem detectionSum_le_mean_add_loss (U V : Finset (Line F))
    (hUV : Disjoint U V) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (hi : ∀ i, i ∉ I i) (a b : U → U → ℝ)
    (η ε : ℝ) (hε : 0 < ε)
    (hXa : ∀ i x, η < z i →
      |conditionalMean U V i x (targetStatistic U V (I i) (J i) x) - a i x| ≤ ε / 2)
    (hYb : ∀ i x, η < z i →
      |conditionalMean U V i x (planeStatistic U V (I i) (J i)) - b i x| ≤ ε / 2) :
    detectionSum U z a b η ε ≤
      (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) +
        loss U V I J z η ε := by
  let : MeasurableSpace (OrderPair U V) := ⊤
  exact (detectionSum_le_cutoffSum U z a b η ε).trans
    (detection_sum_le_mean_firstMarkCount_add_error U V hUV I J z hi a b η ε hε hXa hYb)

def dFinite (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  detectionSum D (zD D)
    (fun i x => dTest (lineProfile D C x) (zD D i))
    (fun i _ => planeTest (planeProfile D C) (zD D i)) η ε / Fintype.card F

def cFinite (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  detectionSum C (zC C)
    (fun i x => cTest (lineProfile D C x) (zC C i))
    (fun i _ => planeTest (planeProfile D C) (zC C i)) η ε / Fintype.card F

theorem finiteDetection_le_normalizedMean_add_bound
    (k : ℕ) (D C : Finset (Line F)) (hp : IsProfilePair k D C)
    (η ε : ℝ) (hε : 0 < ε)
    (hDX : ∀ i x, η < zD D i →
      |conditionalMean D C i x (targetStatistic D C (ID D C i) (JD D C i) x) -
        dTest (lineProfile D C x) (zD D i)| ≤ ε / 2)
    (hDY : ∀ i x, η < zD D i →
      |conditionalMean D C i x (planeStatistic D C (ID D C i) (JD D C i)) -
        planeTest (planeProfile D C) (zD D i)| ≤ ε / 2)
    (hCX : ∀ i x, η < zC C i →
      |conditionalMean C D i x (targetStatistic C D (IC D C i) (JC D C i) x) -
        cTest (lineProfile D C x) (zC C i)| ≤ ε / 2)
    (hCY : ∀ i x, η < zC C i →
      |conditionalMean C D i x (planeStatistic C D (IC D C i) (JC D C i)) -
        planeTest (planeProfile D C) (zC C i)| ≤ ε / 2) :
    dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
      32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  have hD := detectionSum_le_mean_add_loss D C hp.2.1
    (ID D C) (JD D C) (zD D) (current_not_ID D C)
    (fun i x => dTest (lineProfile D C x) (zD D i))
    (fun i _ => planeTest (planeProfile D C) (zD D i)) η ε hε hDX hDY
  have hC := detectionSum_le_mean_add_loss C D hp.2.1.symm
    (IC D C) (JC D C) (zC C) (current_not_IC D C)
    (fun i x => cTest (lineProfile D C x) (zC C i))
    (fun i _ => planeTest (planeProfile D C) (zC C i)) η ε hε hCX hCY
  have hsum := div_le_div_of_nonneg_right (add_le_add hD hC)
    (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have he := total_loss_div_le k D C hp (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) η ε
  have hmean := mean_markCount_eq_add D C (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) η ε
  unfold dFinite cFinite normalizedMean sourceMarkCount
  rw [hmean]
  simp only [add_div] at hsum he ⊢
  linarith

end Balanced.ProfileFiniteMarks

end

end OAI
