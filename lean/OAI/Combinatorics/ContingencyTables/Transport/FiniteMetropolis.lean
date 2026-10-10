import OAI.Combinatorics.ContingencyTables.Transport.RationalReindex

namespace OAI

/-! # Exact finite proposal-and-acceptance experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [Nonempty β] [Nonempty γ]

def finiteAcceptStep (a : α) (proposal : β → Option α) (accept : α → γ → Prop)
    (z : β × γ) : α :=
  match proposal z.1 with
  | none => a
  | some b => if accept b z.2 then b else a

def finiteAcceptLaw (a : α) (proposal : β → Option α) (accept : α → γ → Prop) : RationalLaw α :=
  mapLaw (productLaw (uniformLaw (α := β)) (uniformLaw (α := γ)))
    (finiteAcceptStep a proposal accept)

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [Nonempty β] [Nonempty γ] in
theorem finiteAcceptStep_eq_iff (a b : α) (proposal : β → Option α) (accept : α → γ → Prop)
    (z : β × γ) (hab : a ≠ b) :
    finiteAcceptStep a proposal accept z = b ↔ proposal z.1 = some b ∧ accept b z.2 := by
  cases hp : proposal z.1 with
  | none => simp [finiteAcceptStep, hp, hab]
  | some c =>
    by_cases hcb : c = b
    · subst c
      simp [finiteAcceptStep, hp, hab]
    · by_cases hc : accept c z.2 <;> simp [finiteAcceptStep, hp, hc, hcb, hab]

/-- The off-diagonal mass is the exact product of the proposal-code and
acceptance-coin frequencies. Both experiments use bounded finite samples. -/
theorem finiteAcceptLaw_off_diagonal (a b : α) (proposal : β → Option α)
    (accept : α → γ → Prop) (hab : a ≠ b) :
    (finiteAcceptLaw a proposal accept).mass b =
      ((Finset.univ.filter (fun z => proposal z = some b)).card / (Fintype.card β : ℚ)) *
      ((Finset.univ.filter (accept b)).card / (Fintype.card γ : ℚ)) := by
  change (∑ z : β × γ, if finiteAcceptStep a proposal accept z = b then
    uniformMass (α := β) * uniformMass (α := γ) else 0) = _
  simp_rw [finiteAcceptStep_eq_iff a b proposal accept _ hab]
  rw [Fintype.sum_prod_type]
  have hs : (∑ x : β, ∑ y : γ, if proposal x = some b ∧ accept b y then
      uniformMass (α := β) * uniformMass (α := γ) else 0) =
      (∑ x : β, if proposal x = some b then uniformMass (α := β) else 0) *
      (∑ y : γ, if accept b y then uniformMass (α := γ) else 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : proposal x = some b <;> by_cases hy : accept b y <;> simp [hx, hy]
  rw [hs, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, uniformMass]
  ring

omit [Fintype β] [Fintype γ] [Nonempty β] [Nonempty γ] in
/-- Two finite probability laws agreeing off a fixed state agree there
as well. This recovers the rejection/stay probability from normalization. -/
theorem RationalLaw.eq_of_off_diagonal (p q : RationalLaw α) (a : α)
    (h : ∀ b, b ≠ a → p.mass b = q.mass b) : p = q := by
  apply RationalLaw.ext
  funext b
  by_cases hb : b = a
  · subst b
    have hp := Finset.sum_erase_add (Finset.univ : Finset α) p.mass (Finset.mem_univ a)
    have hq := Finset.sum_erase_add (Finset.univ : Finset α) q.mass (Finset.mem_univ a)
    have he : (∑ b ∈ Finset.univ.erase a, p.mass b) = ∑ b ∈ Finset.univ.erase a, q.mass b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact h b (Finset.mem_erase.mp hb).1
    rw [p.total] at hp
    rw [q.total] at hq
    rw [he] at hp
    linarith
  · exact h b hb

end

end ContingencyTables.FirstSuccess

end OAI
