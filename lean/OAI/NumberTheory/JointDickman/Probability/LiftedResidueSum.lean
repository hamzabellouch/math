import OAI.NumberTheory.JointDickman.Amplification.ReducedArcLifts

namespace OAI

/-! # The finite residue indexing of all reduced arc lifts -/

namespace JointDickman
open Finset

theorem sum_units_eq_coprime {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, f u) = ∑ r : ZMod q, if r.val.Coprime q then f r else 0 := by
  classical
  calc
    _ = ∑ r : {r : ZMod q // r.val.Coprime q}, f r.val := by
      apply Fintype.sum_equiv ZMod.unitsEquivCoprime
      intro u
      rfl
    _ = ∑ r ∈ univ.filter (fun r : ZMod q => r.val.Coprime q), f r :=
      (sum_subtype _ (by simp) f).symm
    _ = _ := by rw [sum_filter]

theorem sum_lifted_locations (j q : ℕ) [NeZero j] [NeZero q] [NeZero (j*q)]
    (G : ℝ → ℂ) :
    (∑ u : (ZMod q)ˣ, ∑ t : Fin j,
      G ((((u : ZMod q).val : ℝ)/q+t.val)/j)) =
      ∑ h : ZMod (j*q), if h.val.Coprime q then G ((h.val : ℝ)/(j*q : ℕ)) else 0 := by
  classical
  calc
    _ = ∑ t : Fin j, ∑ r : ZMod q,
        if r.val.Coprime q then G (((r.val : ℝ)/q+t.val)/j) else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      exact sum_units_eq_coprime (q := q) (fun r => G (((r.val : ℝ)/q+t.val)/j))
    _ = ∑ p : Fin j × Fin q,
        if p.2.val.Coprime q then G (((p.2.val : ℝ)/q+p.1.val)/j) else 0 := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro t _
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro r
      change (if r.val.Coprime q then G (((r.val : ℝ)/q+t.val)/j) else 0) =
        if (ZMod.finEquiv q r).val.Coprime q then
          G ((((ZMod.finEquiv q r).val : ℝ)/q+t.val)/j) else 0
      rw [val_finEquiv]
    _ = _ := by
      apply Fintype.sum_equiv (arcLiftEquiv j q)
      rintro ⟨t,r⟩
      simp only [arcLiftEquiv_coprime,arcLiftEquiv_location]

end JointDickman

end OAI
