import Mathlib
import OAI.Probability.BinarySweep.GridBounds.DiagonalRigidity

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma factorial_le_diagonal_dimension (L : ℕ) (hL : ∀ x : Cell μ, diagonal μ x < L) :
    (Fintype.card (Cell μ)).factorial ≤ L^(Fintype.card (Cell μ)) *
      Module.finrank ℂ (SpechtSpace μ) := by
  let f : Cell μ → Fin L := fun x => ⟨diagonal μ x,hL x⟩
  have hf : fiberStabilizer f = diagonalStabilizer μ := by
    ext g
    constructor
    · intro hg x
      exact congrArg Fin.val (hg x)
    · intro hg x
      exact Fin.ext (hg x)
  have hb := factorial_le_colorings_mul_stabilizer f
  rw [Fintype.card_fin, hf, Nat.card_eq_fintype_card] at hb
  exact hb.trans (Nat.mul_le_mul_left _ (diagonal_card_le_dimension μ))

lemma specht_dimension_pos : 0 < Module.finrank ℂ (SpechtSpace μ) :=
  lt_of_lt_of_le (Fintype.card_pos) (diagonal_card_le_dimension μ)

theorem log_dimension_lower_of_diagonal_bound (L : ℕ) (hpos : 0 < L)
    (hk : 0 < Fintype.card (Cell μ)) (hL : ∀ x : Cell μ, diagonal μ x < L) :
    (Fintype.card (Cell μ) : ℝ) *
        (Real.log (Fintype.card (Cell μ)) - Real.log L - 1) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  let k := Fintype.card (Cell μ)
  let D := Module.finrank ℂ (SpechtSpace μ)
  have hD : (0 : ℝ) < D := by exact_mod_cast specht_dimension_pos μ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hpos
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hbound : (k.factorial : ℝ) ≤ (L : ℝ)^k * D := by
    exact_mod_cast factorial_le_diagonal_dimension μ L hL
  have hlog := Real.log_le_log hfac hbound
  rw [Real.log_mul (pow_ne_zero _ hLr.ne') hD.ne', Real.log_pow] at hlog
  have hst := Stirling.le_log_factorial_stirling (show k ≠ 0 from hk.ne')
  have hpi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hklog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  change (k : ℝ) * (Real.log k - Real.log L - 1) ≤ Real.log D
  nlinarith

lemma diagonal_lt_height_add_width (x : Cell μ) :
    diagonal μ x < μ.colLen 0 + μ.rowLen 0 := by
  have hr : row x < μ.colLen (col x) := YoungDiagram.mem_iff_lt_colLen.mp x.property
  have hc : col x < μ.rowLen (row x) := YoungDiagram.mem_iff_lt_rowLen.mp x.property
  have hr' := μ.colLen_anti 0 (col x) (Nat.zero_le _)
  have hc' := μ.rowLen_anti 0 (row x) (Nat.zero_le _)
  unfold diagonal
  omega

lemma width_add_rectangle_le_card (x : Cell μ) :
    μ.rowLen 0 + row x * (col x+1) ≤ Fintype.card (Cell μ) := by
  let f : Fin (μ.rowLen 0) ⊕ (Fin (row x) × Fin (col x+1)) → Cell μ :=
    Sum.elim (fun a => ⟨(0,a.val), YoungDiagram.mem_iff_lt_rowLen.mpr a.isLt⟩)
      (fun a => ⟨(a.1.val+1,a.2.val), μ.up_left_mem
        (show a.1.val+1 ≤ row x from a.1.isLt)
        (show a.2.val ≤ col x from Nat.le_of_lt_succ a.2.isLt) x.property⟩)
  have hf : Function.Injective f := by
    intro a b he
    have he' := congrArg Subtype.val he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hab : a = b := Fin.ext (congrArg Prod.snd he')
        exact congrArg Sum.inl hab
      | inr b =>
        have hh := congrArg Prod.fst he'
        change 0 = b.1.val+1 at hh
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hh := congrArg Prod.fst he'
        change a.1.val+1 = 0 at hh
        omega
      | inr b =>
        congr 1
        apply Prod.ext
        · apply Fin.ext
          have hh := congrArg Prod.fst he'
          change a.1.val+1 = b.1.val+1 at hh
          omega
        · exact Fin.ext (congrArg Prod.snd he')
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

lemma height_add_rectangle_le_card (x : Cell μ) :
    μ.colLen 0 + col x * (row x+1) ≤ Fintype.card (Cell μ) := by
  let y : Cell μ.transpose := ⟨x.val.swap, YoungDiagram.mem_transpose.mpr x.property⟩
  have hh := width_add_rectangle_le_card μ.transpose y
  have hc : Fintype.card (Cell μ.transpose) = Fintype.card (Cell μ) := by
    simpa only [Cell, Fintype.card_coe, YoungDiagram.card] using YoungDiagram.card_transpose μ
  simpa only [YoungDiagram.rowLen_transpose, hc, y, row, col, Prod.fst_swap, Prod.snd_swap] using hh

lemma height_width_le_card : max (μ.colLen 0) (μ.rowLen 0) ≤ Fintype.card (Cell μ) := by
  by_cases h : Nonempty (Cell μ)
  · obtain ⟨x⟩ := h
    exact max_le (by have := height_add_rectangle_le_card μ x; omega)
      (by have := width_add_rectangle_le_card μ x; omega)
  · have hempty : μ = ⊥ := by
      apply YoungDiagram.ext
      ext x
      simp only [YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
      intro hx
      exact h ⟨⟨x,hx⟩⟩
    subst μ
    simp [YoungDiagram.colLen, YoungDiagram.rowLen]

lemma diagonal_twice_le (x : Cell μ) :
    2*(diagonal μ x+1) ≤ Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0) := by
  have hr : row x < μ.colLen 0 :=
    (YoungDiagram.mem_iff_lt_colLen.mp x.property).trans_le (μ.colLen_anti 0 _ (Nat.zero_le _))
  have hc : col x < μ.rowLen 0 :=
    (YoungDiagram.mem_iff_lt_rowLen.mp x.property).trans_le (μ.rowLen_anti 0 _ (Nat.zero_le _))
  have hm := height_width_le_card μ
  unfold diagonal
  by_cases hrow : row x = 0
  · rw [hrow]
    omega
  by_cases hcol : col x = 0
  · rw [hcol]
    omega
  rcases le_total (μ.colLen 0) (μ.rowLen 0) with h | h
  · rw [max_eq_right h]
    have hh := width_add_rectangle_le_card μ x
    have hm2 : 2*row x ≤ row x*(col x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [max_eq_left h]
    have hh := height_add_rectangle_le_card μ x
    have hm2 : 2*col x ≤ col x*(row x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

lemma diagonal_lt_half_card_add_max (x : Cell μ) :
    diagonal μ x < (Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0))/2 := by
  have hh := diagonal_twice_le μ x
  omega

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

def assembleFiberPerm (f : X → Y) (p : ∀ y, Equiv.Perm {x // f x = y}) :
    fiberStabilizer f :=
  ⟨(Equiv.sigmaFiberEquiv f).permCongr (Equiv.sigmaCongrRight p), by
    intro x
    exact (p (f x) ⟨x,rfl⟩).property⟩

omit [Fintype X] [Fintype Y] in
lemma assembleFiberPerm_injective (f : X → Y) : Function.Injective (assembleFiberPerm f) := by
  intro p q he
  have hh := congrArg Subtype.val he
  have hh' : Equiv.sigmaCongrRight p = Equiv.sigmaCongrRight q :=
    (Equiv.sigmaFiberEquiv f).permCongr.injective hh
  exact Equiv.Perm.sigmaCongrRightHom_injective hh'

lemma product_factorial_le_stabilizer (f : X → Y) :
    (∏ y, (Fintype.card {x // f x = y}).factorial) ≤ Nat.card (fiberStabilizer f) := by
  have hi := Nat.card_le_card_of_injective (assembleFiberPerm f) (assembleFiberPerm_injective f)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_perm] using hi

lemma two_pow_sub_one_le_factorial (n : ℕ) : 2^(n-1) ≤ n.factorial := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_sub_one, pow_succ, Nat.factorial_succ]
      have hp : 2 ≤ n+1+1 := by omega
      simpa only [Nat.succ_sub_one, mul_comm] using Nat.mul_le_mul ih hp

lemma two_pow_card_sub_colors_le_stabilizer (f : X → Y) :
    2^(Fintype.card X - Fintype.card Y) ≤ Nat.card (fiberStabilizer f) := by
  have hsum : ∑ y, Fintype.card {x // f x = y} = Fintype.card X := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hexp : Fintype.card X - Fintype.card Y ≤
      ∑ y, (Fintype.card {x // f x = y} - 1) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (y : Y) _ =>
      show Fintype.card {x // f x = y} ≤ (Fintype.card {x // f x = y} - 1) + 1 from by omega)
    rw [hsum, Finset.sum_add_distrib] at hh
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hh
    omega
  calc
    _ ≤ 2^(∑ y, (Fintype.card {x // f x = y} - 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = ∏ y, 2^(Fintype.card {x // f x = y} - 1) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ y, (Fintype.card {x // f x = y}).factorial :=
      Finset.prod_le_prod (fun y _ => two_pow_sub_one_le_factorial _)
    _ ≤ _ := product_factorial_le_stabilizer f

end BinaryCoordinateSweeps.Young

end

end OAI
