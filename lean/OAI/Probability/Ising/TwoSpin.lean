import OAI.Probability.Ising.Basic

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Walsh coefficients of the log of a positive two-spin table. -/
noncomputable def tableConstant (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false false) +
    Real.log (w true false) + Real.log (w false true)) / 4

noncomputable def tableCoupling (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false false) -
    Real.log (w true false) - Real.log (w false true)) / 4

noncomputable def tableFieldLeft (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w true false) -
    Real.log (w false true) - Real.log (w false false)) / 4

noncomputable def tableFieldRight (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false true) -
    Real.log (w true false) - Real.log (w false false)) / 4

lemma table_expansion (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) (s t : Bool) :
    w s t = Real.exp (tableConstant w + tableCoupling w * spin s * spin t +
      tableFieldLeft w * spin s + tableFieldRight w * spin t) := by
  have H : tableConstant w + tableCoupling w * spin s * spin t +
      tableFieldLeft w * spin s + tableFieldRight w * spin t = Real.log (w s t) := by
    cases s <;> cases t <;>
      simp only [tableConstant, tableCoupling, tableFieldLeft, tableFieldRight, spin_true, spin_false] <;>
      ring
  rw [H, Real.exp_log (hw s t)]

noncomputable def balancedTable (w : Bool → Bool → ℝ) (s t : Bool) : ℝ :=
  w s t * Real.exp (-tableFieldLeft w * spin s - tableFieldRight w * spin t)

lemma balancedTable_eq (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) (s t : Bool) :
    balancedTable w s t = Real.exp (tableConstant w + tableCoupling w * spin s * spin t) := by
  rw [balancedTable, table_expansion w hw s t, ← Real.exp_add]
  congr 1
  ring

noncomputable def tableExpectation (w : Bool → Bool → ℝ) (f : Bool → Bool → ℝ) : ℝ :=
  (∑ s, ∑ t, w s t * f s t) / ∑ s, ∑ t, w s t

lemma balancedTable_means (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) :
    tableExpectation (balancedTable w) (fun s _ => spin s) = 0 ∧
      tableExpectation (balancedTable w) (fun _ t => spin t) = 0 := by
  simp [tableExpectation, balancedTable_eq w hw, spin]
  constructor; ring

lemma balancedTable_correlation (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) :
    tableExpectation (balancedTable w) (fun s t => spin s * spin t) =
      Real.tanh (tableCoupling w) := by
  simp [tableExpectation, balancedTable_eq w hw, spin, Real.exp_add]
  rw [Real.tanh_eq]
  have hC := (Real.exp_pos (tableConstant w)).ne'
  have hK := (add_pos (Real.exp_pos (tableCoupling w))
    (Real.exp_pos (-tableCoupling w))).ne'
  field_simp
  ring

end BufferedIsing

end OAI
