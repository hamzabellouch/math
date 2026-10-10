import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyResidues
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotPolynomials

namespace OAI

/-! # Frequency support depends only on bulk residue classes -/

namespace Ostmann
open scoped Classical

def MovingSlotData.CompensationAgreement {σ : Type*} (v w : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ u left right =>
      MovingSlotReversal.naturalProduct v u = MovingSlotReversal.naturalProduct w u ∧
        left.CompensationAgreement v w ∧ right.CompensationAgreement v w

theorem MovingSlotData.compensationAgreement_of_eq_off {σ : Type*}
    (v w : σ → ℕ) (S : Set σ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (hvalue : ∀ i ∉ S, v i = w i) :
    T.CompensationAgreement v w := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    refine ⟨?_, ihL (fun i hi => (hT i hi).2.1), ihR (fun i hi => (hT i hi).2.2)⟩
    unfold MovingSlotReversal.naturalProduct
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hvalue i (fun hS => (hT i hS).1 hi)

theorem naturalProduct_modEq_values {σ : Type*} (v w : σ → ℕ) (M : ℤ)
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD M]) (s : List σ) :
    (MovingSlotReversal.naturalProduct v s : ℤ) ≡
      (MovingSlotReversal.naturalProduct w s : ℤ) [ZMOD M] := by
  induction s with
  | nil => exact Int.ModEq.refl _
  | cons i s ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons,
      Nat.cast_mul] using (h i).mul ih

theorem MovingSlotReversal.signedNumerator_values_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (v w : σ → ℕ) (M XL XR YL YR : ℤ)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD M])
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    s.signedNumerator v XL XR ≡ s.signedNumerator w YL YR [ZMOD M] := by
  exact ((hR.mul (naturalProduct_modEq_values v w M hv s.rightSlots)).mul_left _).sub
    ((hL.mul (naturalProduct_modEq_values v w M hv s.leftSlots)).mul_left _)

theorem MovingSlotReversal.frequencyPivot_values_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (v w : σ → ℕ) (R : ℤ) (k : ℕ)
    (hs : s.rootFrequency ≠ 0) (hsR : s.rootFrequency ∣ R)
    (hc : MovingSlotReversal.naturalProduct v s.compensationSlots =
      MovingSlotReversal.naturalProduct w s.compensationSlots)
    (XL XR YL YR : ℤ)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (k + 1)])
    (hL : XL ≡ YL [ZMOD R ^ (k + 1)]) (hR : XR ≡ YR [ZMOD R ^ (k + 1)]) :
    s.frequencyPivot v R k XL XR ≡ s.frequencyPivot w R k YL YR [ZMOD R ^ k] := by
  have hd : s.rootFrequency * R ^ k ∣ R ^ (k + 1) := by
    simpa only [pow_succ, mul_comm] using mul_dvd_mul hsR (dvd_refl (R ^ k))
  have hn := s.signedNumerator_values_modEq v w _ XL XR YL YR hv hL hR
  unfold frequencyPivot
  rw [hc]
  exact (int_modEq_ediv _ _ _ _ hs (hn.of_dvd hd)).mul_right _

/-- All frequency divisibility and unit tests survive simultaneous bulk
replacement. Only one frequency power is consumed at each tree level. -/
theorem movingFrequencyGate_values_modEq {σ : Type*} (v w : σ → ℕ) (R : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hcomp : T.CompensationAgreement v w) (hR : T.frequencyProduct ∣ R)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)])
    (XL XR YL YR : ℤ) (hL : XL ≡ YL [ZMOD R ^ (n + 1)])
    (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyGate v R T XL XR ↔ movingFrequencyGate w R T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    exact movingFrequencyLocalUnits_modEq _ _ _ _ _ _ (by simpa using hR) hL hRight
  | @node n s CL CR u left right ihL ihR =>
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR u left right R hR
    let step := MovingSlotData.step s CL CR u left right false
    have hp := step.frequencyPivot_values_modEq v w R (n + 1) hf.1 hd.1 hcomp.1
      XL XR YL YR hv hL hRight
    have hpow : R ∣ R ^ (n + 1 + 1) := dvd_pow_self R (by omega)
    have hn := step.signedNumerator_values_modEq v w _ XL XR YL YR hv hL hRight
    have hdiv := (hn.of_dvd (hd.1.trans hpow)).dvd_iff
    have hlocal := movingFrequencyLocalUnits_modEq
      (MovingSlotData.node s CL CR u left right) XL XR YL YR _ (hR.trans hpow) hL hRight
    have hdown : R ^ (n + 1) ∣ R ^ (n + 1 + 1) := pow_dvd_pow R (by omega)
    change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    exact and_congr hlocal (and_congr hdiv (and_congr
      (ihL hf.2.1 hcomp.2.1 hd.2.1 (fun i => (hv i).of_dvd hdown)
        _ _ _ _ hp (hL.of_dvd hdown))
      (ihR hf.2.2 hcomp.2.2 hd.2.2 (fun i => (hv i).of_dvd hdown)
        _ _ _ _ hp (hRight.of_dvd hdown))))

end Ostmann

end OAI
