import OAI.Analysis.LipschitzHilbert.Phase.PhaseCombinatorics
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Cardinality of separated frequencies in one bounded interval. -/

noncomputable section

namespace LipschitzHilbert.PhaseCombinatorics

theorem ordered_separated_index_bound {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (hf : StrictMono f) {gap : ℝ} (hsep : Separated f gap) (i : Fin N) :
    (i.val : ℝ) * gap ≤ f i - f ⟨0, hN⟩ := by
  have h (k : ℕ) (hk : k < N) : (k : ℝ) * gap ≤ f ⟨k, hk⟩ - f ⟨0, hN⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < N := by omega
      have hstep := @hsep (⟨k + 1, hk⟩ : Fin N) ⟨k, hk'⟩ (by
        intro heq
        have hv := congrArg Fin.val heq
        change k + 1 = k at hv
        omega)
      have hmono : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf (by
        change k < k + 1
        omega)
      rw [abs_of_pos (sub_pos.mpr hmono)] at hstep
      have hprev := ih hk'
      push_cast
      nlinarith
  exact h i.val i.isLt

theorem separated_card_le_span {ι : Type*} [Fintype ι] (frequency : ι → ℝ)
    {gap a b : ℝ} (hgap : 0 < gap) (hab : a ≤ b)
    (hsep : Separated frequency gap) (hbound : ∀ i, a ≤ frequency i ∧ frequency i ≤ b) :
    (Fintype.card ι : ℝ) ≤ 1 + (b - a) / gap := by
  classical
  by_cases hN : Fintype.card ι = 0
  · rw [hN]
    have hdiv := div_nonneg (sub_nonneg.mpr hab) hgap.le
    norm_num
    linarith
  · have hNpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hN
    have hinj : Function.Injective frequency := by
      intro i j hij
      by_contra hne
      have h := @hsep i j hne
      rw [hij, sub_self, abs_zero] at h
      linarith
    let : LinearOrder ι := LinearOrder.lift' frequency hinj
    let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
    have hf : StrictMono (fun i => frequency (e i)) := fun _ _ hij => e.strictMono hij
    have he_sep : Separated (fun i => frequency (e i)) gap := by
      intro i j hij
      exact @hsep (e i) (e j) (fun h => hij (e.injective h))
    let last : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hindex := ordered_separated_index_bound hNpos _ hf he_sep last
    have hspan : ((Fintype.card ι : ℝ) - 1) * gap ≤ b - a := by
      have hlast := (hbound (e last)).2
      have hfirst := (hbound (e ⟨0, hNpos⟩)).1
      dsimp only [last] at hindex
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one] at hindex
      linarith
    have hdiv := (le_div_iff₀ hgap).2 hspan
    linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
