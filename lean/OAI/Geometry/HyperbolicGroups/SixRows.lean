import Mathlib
import OAI.Geometry.HyperbolicGroups.FiberLaw
import OAI.Geometry.HyperbolicGroups.SixCounts

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Rows (w : (Fin 6 → A) → Bool) (u : A) :=
  {x : Fin 6 → A // x 0 = u ∧ w x = true}

instance (w : (Fin 6 → A) → Bool) (u : A) : Fintype (Rows w u) :=
  inferInstanceAs (Fintype {entry : Fin 6 → A // entry 0 = u ∧ w entry = true})

def row (w : (Fin 6 → A) → Bool) (u : A) (x : Rows w u) (j : Fin 5) : A := x.val j.succ

lemma card_row_fiber (w : (Fin 6 → A) → Bool) (u v : A) (j : Fin 5) :
    (Fintype.card {x : Rows w u // row w u x j = v} : ℝ) = count 0 j.succ u v w := by
  classical
  let e : {x : Rows w u // row w u x j = v} ≃
      {x : Fin 6 → A // x 0 = u ∧ x j.succ = v ∧ w x = true} :=
    { toFun x := ⟨x.val.val, x.val.property.1, x.property, x.val.property.2⟩
      invFun x := ⟨⟨x.val,x.property.1,x.property.2.2⟩,x.property.2.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  unfold count
  rw [← Finset.sum_filter]
  simp only [Nat.cast_sum,Nat.cast_one,Finset.card_eq_sum_ones]
  apply Finset.sum_congr
  · ext x
    simp [mem_pairTrials (Ne.symm (Fin.succ_ne_zero j)), and_assoc]
  · simp

lemma row_card_sum (w : (Fin 6 → A) → Bool) (u : A) (j : Fin 5) :
    (Fintype.card (Rows w u) : ℝ) = ∑ v : A, count 0 j.succ u v w := by
  simp_rw [← card_row_fiber]
  rw [← Nat.cast_sum,FiniteLaw.card_fibers]

lemma count_bounds {δ τ : ℝ} {w : (Fin 6 → A) → Bool} (h : ¬BadPairs δ τ w)
    {r q : Fin 6} (hr : r ≠ q) (u v : A) :
    (1-τ)*(Fintype.card A:ℝ)^(1-δ) < count r q u v w ∧
    count r q u v w < (1+τ)*(Fintype.card A:ℝ)^(1-δ) := by
  have hh : |count r q u v w - (Fintype.card A:ℝ)^(1-δ)| <
      τ*(Fintype.card A:ℝ)^(1-δ) := lt_of_not_ge (fun hh => h ⟨⟨(r,q),hr⟩,u,v,hh⟩)
  rcases abs_lt.mp hh with ⟨h₁,h₂⟩
  constructor <;> nlinarith

variable [Nonempty A]

lemma rows_nonempty {δ τ : ℝ} {w : (Fin 6 → A) → Bool}
    (hτ : τ < 1) (h : ¬BadPairs δ τ w) (u : A) : Nonempty (Rows w u) := by
  have hp : 0 < (Fintype.card A:ℝ)^(1-δ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _
  have hh := (count_bounds h (show (0 : Fin 6) ≠ (0 : Fin 5).succ by decide)
    u (Classical.choice inferInstance)).1
  have hx : 0 < count 0 (0 : Fin 5).succ u (Classical.choice inferInstance) w :=
    (mul_pos (sub_pos.mpr hτ) hp).trans hh
  rw [← card_row_fiber] at hx
  have hn : Nonempty {x : Rows w u // row w u x 0 = (Classical.choice inferInstance : A)} :=
    Fintype.card_pos_iff.mp (by exact_mod_cast hx)
  exact hn.map Subtype.val

/-- The literal uniform law on the six-letter relators with first letter u has
all five remaining marginal densities at most twice uniform. -/
theorem marginal_bound {δ τ : ℝ} {w : (Fin 6 → A) → Bool}
    (hτ : τ ≤ 1/3) (h : ¬BadPairs δ τ w) (u : A) :
    letI := rows_nonempty (by linarith : τ < 1) h u
    ∀ j v, (((FiniteLaw.uniform : FiniteLaw (Rows w u)).map (fun x => row w u x j)).mass v)
      ≤ 2 / Fintype.card A := by
  let := rows_nonempty (by linarith : τ < 1) h u
  intro j v
  rw [FiniteLaw.uniform_map_mass,card_row_fiber]
  have hn : 0 < (Fintype.card A:ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  have hr : 0 < (Fintype.card (Rows w u):ℝ) := by exact_mod_cast Fintype.card_pos (α := Rows w u)
  have hp : 0 < (Fintype.card A:ℝ)^(1-δ) := Real.rpow_pos_of_pos hn _
  have hx := (count_bounds h (Ne.symm (Fin.succ_ne_zero j)) u v).2.le
  have hsum : (Fintype.card A:ℝ)*((1-τ)*(Fintype.card A:ℝ)^(1-δ)) ≤
      (Fintype.card (Rows w u):ℝ) := by
    rw [row_card_sum w u j]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
        (count_bounds h (Ne.symm (Fin.succ_ne_zero j)) u v).1.le)
  rw [div_le_div_iff₀ hr hn]
  have ha : (1+τ)*(Fintype.card A:ℝ)^(1-δ) ≤
      2*((1-τ)*(Fintype.card A:ℝ)^(1-δ)) := by nlinarith
  calc
    count 0 j.succ u v w * Fintype.card A ≤
        (2*((1-τ)*(Fintype.card A:ℝ)^(1-δ)))*Fintype.card A :=
      mul_le_mul_of_nonneg_right (hx.trans ha) hn.le
    _ = 2*((Fintype.card A:ℝ)*((1-τ)*(Fintype.card A:ℝ)^(1-δ))) := by ring
    _ ≤ 2*Fintype.card (Rows w u) := mul_le_mul_of_nonneg_left hsum (by norm_num)

end SixTable
end HyperbolicObstruction
end
end

section

end
end

end OAI
