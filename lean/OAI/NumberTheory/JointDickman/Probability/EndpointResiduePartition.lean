import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass
import OAI.NumberTheory.JointDickman.Probability.ResidueFourierParseval
import OAI.NumberTheory.JointDickman.Amplification.AdditivePhaseBridge

namespace OAI

/-! # Exact residue decomposition of the endpoint exponential sums -/

namespace JointDickman
open Finset

theorem residue_nat_phase {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (h*(n : ZMod q)) = additivePhase ((n : ℝ)*h.val/q) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val h,← Nat.cast_mul,stdAddChar_as_additivePhase]
  push_cast
  congr 1
  ring

/-- The residue phase is kept exactly when integers are assigned to cells.
Only the slowly varying archimedean factor is averaged later. -/
theorem endpoint_residue_partition {D : Type*} [Fintype D] [DecidableEq D]
    {B q : ℕ} [NeZero q] (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (s : Finset ℕ) (J : Finset D) (c : ℕ → ℂ) (h : ZMod q) (ν : ℝ)
    (hsupp : ∀ n ∈ s, c n ≠ 0 → ∃ i ∈ J, ∃ r : (ZMod q)ˣ,
      logResidueCell B q lower upper n = some (i,r)) :
    (∑ n ∈ s, c n*additivePhase ((n : ℝ)*(h.val/(q : ℝ)+ν))) =
      unitResidueFourier (fun r => ∑ i ∈ J, ∑ n ∈ s,
        if logResidueCell B q lower upper n = some (i,r)
        then c n*additivePhase ((n : ℝ)*ν) else 0) h := by
  classical
  unfold unitResidueFourier
  simp only [mul_sum]
  simp_rw [sum_comm (s := J) (t := s)]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases hc : c n = 0
  · simp [hc]
  obtain ⟨i,hi,r,hr⟩ := hsupp n hn hc
  have hmod := ((logResidueCell_eq_some B q lower upper hdisjoint n i r).mp hr).2
  have hone : (∑ t : (ZMod q)ˣ, ∑ j ∈ J,
      ZMod.stdAddChar (h*(t : ZMod q))*
        (if logResidueCell B q lower upper n = some (j,t)
        then c n*additivePhase ((n : ℝ)*ν) else 0)) =
        ZMod.stdAddChar (h*(r : ZMod q))*(c n*additivePhase ((n : ℝ)*ν)) := by
    simp only [hr,Option.some.injEq,Prod.mk.injEq]
    rw [sum_eq_single r]
    · rw [sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · exact fun hni => False.elim (hni hi)
    · intro t _ htr
      simp [Ne.symm htr]
    · simp
  rw [hone,← hmod,residue_nat_phase]
  rw [show (n : ℝ)*(h.val/(q : ℝ)+ν) = (n : ℝ)*h.val/q+(n : ℝ)*ν by ring,
    additivePhase_add]
  ring

end JointDickman

end OAI
