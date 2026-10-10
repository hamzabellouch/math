import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateLocality

namespace OAI

/-! A qubit's initialization check can be placed immediately before its first gate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem QMALocalOn.entry_zero_of_outside {n : ℕ} {S : Finset (Fin n)}
    {M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ}
    (hM : QMALocalOn S M) {i : Fin n} (hi : i ∉ S)
    (s t : SourceSpinBasis n) (hst : s i ≠ t i) : M s t = 0 := by
  obtain ⟨A,rfl⟩ := hM
  rw [qmaLocalLift_apply]
  have h : (fun k : {k // k ∉ S} => s k.val) ≠ (fun k : {k // k ∉ S} => t k.val) := by
    intro he
    exact hst (congrFun he ⟨i,hi⟩)
  simp [h]

theorem qmaLocal_mask_commute {n : ℕ} {S : Finset (Fin n)}
    {M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ}
    (hM : QMALocalOn S M) {i : Fin n} (hi : i ∉ S) (P : Fin 2 → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaMask (fun s => P (s i)) (qmaApplyMatrix M u) =
      qmaApplyMatrix M (qmaMask (fun s => P (s i)) u) := by
  ext s
  change (if P (s i) then ∑ t, M s t*u t else 0) =
    ∑ t, M s t*(if P (t i) then u t else 0)
  by_cases hs : P (s i)
  · rw [ite_eq_left hs]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : P (t i)
    · simp [ht]
    · have he : s i ≠ t i := fun h => ht (h ▸ hs)
      simp [ht,hM.entry_zero_of_outside hi s t he]
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : P (t i)
    · have he : s i ≠ t i := fun h => hs (h ▸ ht)
      simp [ht,hM.entry_zero_of_outside hi s t he]
    · simp [ht]

theorem qmaGateProduct_mask_commute (work : ℕ) (gs : List QMAGate)
    (i : Fin (work+1)) (hi : ∀ g ∈ gs, i ∉ qmaGateSites work g)
    (P : Fin 2 → Prop) (u : EuclideanSpace ℂ (SourceSpinBasis (work+1))) :
    qmaMask (fun s => P (s i)) (qmaApplyMatrix (qmaGateProduct work gs) u) =
      qmaApplyMatrix (qmaGateProduct work gs) (qmaMask (fun s => P (s i)) u) := by
  induction gs using List.reverseRecOn with
  | nil => simp [qmaGateProduct_nil]
  | append_singleton gs g ih =>
    simp only [qmaGateProduct_append,qmaGateProduct_singleton,qmaApplyMatrix_mul]
    rw [qmaLocal_mask_commute (qmaGateMatrix_local work g)
      (hi g (by simp)) P,ih (fun g hg => hi g (by simp [hg]))]

theorem qmaInputCheck_prefix_untouched (c : QMACircuit) (hc : c.WellFormed)
    (i : Fin (c.work+1)) (t : ℕ)
    (hi : ∀ g ∈ c.gates.take t, i ∉ qmaGateSites c.work g)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c t) u)‖ =
      ‖qmaMask (qmaInputCheck c i) u‖ := by
  have h := qmaGateProduct_mask_commute c.work (c.gates.take t) i hi
    (fun b => c.witness ≤ i.val ∧ b ≠ 0) u
  change qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c t) u) =
    qmaApplyMatrix (qmaPrefixMatrix c t) (qmaMask (qmaInputCheck c i) u) at h
  rw [h,qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc t)]

theorem qmaDistributedHistoryEnergy_sound_untouched (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i), i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaDistributedHistoryEnergy c τ u :=
  qmaDistributedHistoryEnergy_sound c hc τ hτ
    (fun i v => qmaInputCheck_prefix_untouched c hc i (τ i) (hi i) v) hsound u

end ContinuumCoulomb

end

end OAI
