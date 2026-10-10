import OAI.NumberTheory.CubicMoment.Estimates.LogNormCells

namespace OAI

/-! The actual log-norm cells meeting the product boundary have degree at
most five. The near-cell diagonal therefore retains the inverse cell width. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma scaled_log_product (a b : Eisenstein) (ha : a ≠ 0) (hb : b ≠ 0)
    (J : ℝ) {A B X₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    J*Real.log (norm a/A)+J*Real.log (norm b/B)-J*Real.log (X₀/(A*B)) =
      J*Real.log (norm (a*b)/X₀) := by
  have han : norm a ≠ 0 := norm_eq_zero_iff.not.mpr ha
  have hbn : norm b ≠ 0 := norm_eq_zero_iff.not.mpr hb
  rw [show norm (a*b) = norm a*norm b from Complex.normSq_mul _ _,
    Real.log_div han hA.ne',Real.log_div hbn hB.ne',
    Real.log_div hX.ne' (mul_ne_zero hA.ne' hB.ne'),
    Real.log_div (mul_ne_zero han hbn) hX.ne',
    Real.log_mul han hbn,Real.log_mul hA.ne' hB.ne']
  ring

def nearLogNormCells (P S : Finset Eisenstein) (J A B X₀ : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((P.image (logNormCell J A)).product (S.image (logNormCell J B))).filter
    (fun e => ∃ a ∈ P, ∃ b ∈ S, logNormCell J A a = e.1 ∧
      logNormCell J B b = e.2 ∧ |J*Real.log (norm (a*b)/X₀)| ≤ 1)

lemma nearLogNormCells_offsets (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (J : ℝ) {A B X₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    ∀ e ∈ nearLogNormCells P S J A B X₀,
      e.1+e.2 ∈ nearCellOffsets (J*Real.log (X₀/(A*B))) := by
  intro e he
  obtain ⟨a,ha,b,hb,hai,hbj,hn⟩ := (Finset.mem_filter.mp he).2
  have hx := logNormCell_bounds J A a
  have hy := logNormCell_bounds J B b
  rw [hai] at hx
  rw [hbj] at hy
  rw [←scaled_log_product a b (primary_ne_zero (hP a ha))
    (primary_ne_zero (hS b hb)) J hA hB hX] at hn
  exact nearCell_index_mem ⟨hx.1,hx.2.le⟩ ⟨hy.1,hy.2.le⟩ hn

theorem nearLogNormCells_energy_bound (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (α β : Eisenstein → ℂ) (J : ℝ) {A B X₀ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    (∑ e ∈ nearLogNormCells P S J A B X₀,
      Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)*
      Real.sqrt (∑ b ∈ logNormCellSupport S J B e.2, ‖β b‖^2)) ≤
      5*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  classical
  let E := nearLogNormCells P S J A B X₀
  have he := nearLogNormCells_offsets P S hP hS J hA hB hX
  have hrow (i : ℤ) : (E.filter (fun e => e.1 = i)).card ≤ 5 :=
    nearCell_row_degree E _ he i
  have hcol (j : ℤ) : (E.filter (fun e => e.2 = j)).card ≤ 5 :=
    nearCell_column_degree E _ he j
  have hm := near_cell_sum_le (P.image (logNormCell J A)) (S.image (logNormCell J B)) E
    (fun i => Real.sqrt (∑ a ∈ logNormCellSupport P J A i, ‖α a‖^2))
    (fun j => Real.sqrt (∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2)) 5
    (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
    (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2)
    (fun i _ => hrow i) (fun j _ => hcol j)
  simpa only [logNormCell_energy,Nat.cast_ofNat] using hm

end CubicFirstMoment

end

end OAI
