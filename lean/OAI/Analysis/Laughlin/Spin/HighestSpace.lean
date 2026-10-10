import Mathlib.Algebra.BigOperators.Field
import OAI.Analysis.Laughlin.Spin.Highest2

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero (A B z : ℕ) :
    highestRaw A B z 0 = 1 / Real.sqrt (B.choose z : ℝ) := by
  simp [highestRaw]

theorem highestRaw_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestRaw A B z p ≠ 0 := by
  rw [highestRaw,ite_eq_left hp]
  apply div_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hp))
  · apply ne_of_gt; apply Real.sqrt_pos.mpr
    have ha : 0 < (A.choose p : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
    have hb : 0 < (B.choose (z-p) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : z-p ≤ B)
    positivity

theorem highest_unique (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : ℕ → ℝ)
    (hf : ∀ p < z, ladder A p*f (p+1)+ladder B (z-p-1)*f p = 0) :
    ∀ p ≤ z, f p = (f 0 / highestRaw A B z 0)*highestRaw A B z p := by
  intro p hp
  induction p with
  | zero => field_simp [highestRaw_ne_zero A B z 0 hA hB (by omega)]
  | succ p ih =>
    have hlt : p < z := by omega
    have he := highestRaw_raising A B z p hA hB hlt
    have hh := hf p hlt
    have hi := ih (by omega)
    have ha : ladder A p ≠ 0 := ne_of_gt (ladder_pos A p (by omega))
    apply (mul_left_cancel₀ ha)
    linear_combination hh - (f 0 / highestRaw A B z 0)*he - ladder B (z-p-1)*hi

noncomputable def highestNorm (A B z : ℕ) : ℝ :=
  Real.sqrt (∑ p ∈ Finset.range (z+1), (highestRaw A B z p)^2)

noncomputable def highestUnit (A B z p : ℕ) : ℝ :=
  highestRaw A B z p / highestNorm A B z

theorem highestNorm_pos (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    0 < highestNorm A B z := by
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro p hp; exact sq_nonneg _
  · exact ⟨0,Finset.mem_range.mpr (by omega),sq_pos_of_ne_zero
      (highestRaw_ne_zero A B z 0 hA hB (by omega))⟩

theorem highestUnit_norm (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (∑ p ∈ Finset.range (z+1), (highestUnit A B z p)^2) = 1 := by
  simp only [highestUnit,div_pow,← Finset.sum_div]
  rw [highestNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply div_self
  have h := highestNorm_pos A B z hA hB
  exact ne_of_gt (Real.sqrt_pos.mp h)

theorem highestUnit_raising (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    ladder A p*highestUnit A B z (p+1)+ladder B (z-p-1)*highestUnit A B z p = 0 := by
  simp only [highestUnit,← mul_div_assoc,← add_div]
  rw [highestRaw_raising A B z p hA hB hp,zero_div]

theorem highestUnit_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestUnit A B z p ≠ 0 :=
  div_ne_zero (highestRaw_ne_zero A B z p hA hB hp)
    (ne_of_gt (highestNorm_pos A B z hA hB))

theorem highestUnit_ratio (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    highestUnit A B z (p+1) / highestUnit A B z p =
      -(ladder B (z-p-1) / ladder A p) := by
  have he := highestUnit_raising A B z p hA hB hp
  have ha := ne_of_gt (ladder_pos A p (by omega))
  have hs := highestUnit_ne_zero A B z p hA hB (by omega)
  apply (div_eq_iff hs).mpr
  apply (mul_left_cancel₀ ha)
  field_simp
  nlinarith only [he]

noncomputable def raiseSlice (A B z : ℕ) (f : Fin (z+1) → ℝ) (p : Fin z) : ℝ :=
  ladder A p.val * f ⟨p.val+1,by omega⟩ +
    ladder B (z-p.val-1)*f ⟨p.val,by omega⟩

theorem raiseSlice_kernel (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) :
    (∀ p, raiseSlice A B z f p = 0) ↔
      ∃ c : ℝ, ∀ p, f p = c*highestUnit A B z p.val := by
  constructor
  · intro hf
    let g : ℕ → ℝ := fun p => if h : p < z+1 then f ⟨p,h⟩ else 0
    have hg : ∀ p < z, ladder A p*g (p+1)+ladder B (z-p-1)*g p = 0 := by
      intro p hp
      simpa [g,raiseSlice,hp,show p ≤ z by omega] using hf ⟨p,hp⟩
    refine ⟨(g 0 / highestRaw A B z 0)*highestNorm A B z,?_⟩
    intro p
    have he := highest_unique A B z hA hB g hg p.val (by omega)
    have hn := ne_of_gt (highestNorm_pos A B z hA hB)
    have hfval : g p.val = f p := by simp [g,show p.val ≤ z by omega]
    rw [hfval] at he
    rw [he]
    unfold highestUnit
    field_simp
  · rintro ⟨c,hc⟩ p
    simp only [raiseSlice,hc]
    linear_combination c * highestUnit_raising A B z p.val hA hB p.isLt

end Laughlin.Spin

end OAI
