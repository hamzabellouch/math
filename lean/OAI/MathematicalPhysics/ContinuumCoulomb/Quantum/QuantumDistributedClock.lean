import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireIntertwining
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryEmbedding

namespace OAI

/-! Local initialization checks at arbitrary unary-clock positions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaClockAt (T : ℕ) (t : Fin (T+1)) (s : SourceSpinBasis (T+2)) : Prop :=
  s t.castSucc = 1 ∧ s t.succ = 0

theorem qmaClockAt_history (T : ℕ) (t u : Fin (T+1)) :
    qmaClockAt T t (qmaHistoryClock T u) ↔ u = t := by
  simp only [qmaClockAt,qmaHistoryClock,qmaUnaryClock,Fin.val_castSucc,Fin.val_succ]
  constructor
  · intro ⟨h₁,h₂⟩
    have ha : t.val < u.val+1 := by
      by_contra h
      simp [h] at h₁
    have hb : ¬t.val+1 < u.val+1 := by
      intro h
      simp [h] at h₂
    apply Fin.ext
    omega
  · rintro rfl
    simp

def qmaUnaryDistributedInput (c : QMACircuit) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ i : Fin (c.work+1), ∑ s : SourceSpinBasis (c.gates.length+2),
    if qmaClockAt c.gates.length (τ i) s then
      ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
        Complex.normSq (u (s,a)) else 0 else 0

theorem qmaUnaryDistributedInput_nonneg (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    0 ≤ qmaUnaryDistributedInput c τ u := by
  unfold qmaUnaryDistributedInput
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro s _
  split
  · apply Finset.sum_nonneg
    intro a _
    split
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  · exact le_rfl

theorem qmaUnaryDistributedInput_restrict (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaDistributedInput c (fun i => (τ i).val)
      (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤ qmaUnaryDistributedInput c τ u := by
  unfold qmaDistributedInput qmaUnaryDistributedInput
  apply Finset.sum_le_sum
  intro i _
  rw [qmaMask_norm_sq]
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if qmaClockAt c.gates.length (τ i) s then
        ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
          Complex.normSq (u (s,a)) else 0 else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length (τ i))
    (by
      intro s _
      split
      · apply Finset.sum_nonneg
        intro a _
        split
        · exact Complex.normSq_nonneg _
        · exact le_rfl
      · exact le_rfl) (Finset.mem_univ _)
  have hs : (∑ a : SourceSpinBasis (c.work+1),
      if qmaInputCheck c i a then
        ‖qmaHistoryFromVector c (qmaUnaryRestrict c u) (τ i).val a‖^2 else 0) =
      ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
        Complex.normSq (u (qmaHistoryClock c.gates.length (τ i),a)) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [qmaHistoryFromVector_fin]
    simp only [qmaUnaryRestrict,Complex.sq_norm]
  rw [hs]
  simpa only [qmaClockAt_history,ite_true] using h

def qmaUnaryDistributedEnergy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  qmaUnaryClockEnergy c u+qmaUnaryOutputEnergy c u+14*qmaUnaryDistributedInput c τ u+
    (14*(c.work+1)+8)*c.gates.length*qmaUnaryPropagationEnergy c u

theorem qmaUnaryDistributedEnergy_restrict (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (qmaUnaryRestrict c u))+qmaUnaryClockEnergy c u ≤
      qmaUnaryDistributedEnergy c τ u := by
  have hi := qmaUnaryDistributedInput_restrict c τ u
  have ho := qmaUnaryOutputEnergy_valid_le c u
  have hp := mul_le_mul_of_nonneg_left (qmaUnaryPropagationEnergy_valid_le c u)
    (by positivity : 0 ≤ (14*(c.work+1)+8:ℝ)*c.gates.length)
  unfold qmaDistributedHistoryEnergy qmaUnaryDistributedEnergy
  linarith

theorem qmaUnaryDistributedEnergy_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) (u : QMAUnaryBasis c → ℂ) :
    2*qmaUnaryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaUnaryDistributedEnergy c τ u := by
  have hs := qmaDistributedHistoryEnergy_sound_untouched c hc (fun i => (τ i).val)
    (fun i => Nat.le_of_lt_succ (τ i).isLt) hi hsound
    (qmaHistoryFromVector c (qmaUnaryRestrict c u))
  rw [qmaHistoryFromVector_mass] at hs
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm] at hs
  have hb := qmaUnaryInvalidMass_le c u
  have hn := qmaUnaryInvalidMass_nonneg c u
  have hcoef : (2:ℝ) ≤ 5*(c.gates.length+1:ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) c.gates.length
    linarith
  have hb' : 2*qmaUnaryInvalidMass c u ≤
      5*(c.gates.length+1:ℝ)*qmaUnaryClockEnergy c u :=
    (mul_le_mul_of_nonneg_right hcoef hn).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  have he := mul_le_mul_of_nonneg_left (qmaUnaryDistributedEnergy_restrict c τ u)
    (by positivity : 0 ≤ 5*(c.gates.length+1:ℝ))
  rw [qmaUnaryMass_split]
  linarith

end ContinuumCoulomb

end

end OAI
