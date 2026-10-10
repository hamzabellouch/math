import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactTemplates
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! An explicit one-variable continuation for independent contact lengths.
Four sloping links share a transverse height; the other five remain axial.
Thus each nine-link path is adjusted by one scalar intermediate-value solve,
with fixed endpoints and no solve whose dimension grows with the lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def contactLengthTolerance : ℝ := 1 / 100000000

def contactHeightLow (c : ℝ) : ℝ := Real.sqrt (1 - (c + 1 / 1000) ^ 2)
def contactHeightHigh (c : ℝ) : ℝ := Real.sqrt (1 - (c - 1 / 1000) ^ 2)

def adjustedContactForward (length h : ℝ) : ℝ := Real.sqrt (length ^ 2 - h ^ 2)

def adjustedContactStepX (lengths : ℕ → ℝ) (h : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then adjustedContactForward (lengths k) h
  else lengths k

def adjustedContactStepY (h : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 then h else if k = 5 ∨ k = 6 then -h else 0

def adjustedContactVertex (lengths : ℕ → ℝ) (h : ℝ) (k : ℕ) : ContactPoint :=
  contactPoint (∑ j ∈ Finset.range k, adjustedContactStepX lengths h j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h j)

def adjustedContactSpan (lengths : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 9, adjustedContactStepX lengths h j

/-- A quantitative square-root estimate, with fixed rational margins. -/
theorem adjustedContactForward_bound {length c h : ℝ}
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance)
    (hc : 7 / 10 ≤ c) (hc' : c ≤ 9 / 10) (hh : h ^ 2 = 1 - c ^ 2) :
    c - 1 / 10000 ≤ adjustedContactForward length h ∧
      adjustedContactForward length h ≤ c + 1 / 10000 := by
  have hlnonneg : 0 ≤ length := by unfold contactLengthTolerance at hl; linarith
  have hlo : (1 - contactLengthTolerance) ^ 2 ≤ length ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ length + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hhi : length ^ 2 ≤ (1 + contactLengthTolerance) ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl')
      (show 0 ≤ (1 + contactLengthTolerance) + length by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
  have hrad : 0 ≤ length ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hlo
    nlinarith
  have hs : adjustedContactForward length h ^ 2 = length ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsnonneg : 0 ≤ adjustedContactForward length h := Real.sqrt_nonneg _
  unfold contactLengthTolerance at hlo hhi
  constructor <;> nlinarith

theorem contactHeightLow_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ^ 2 = 1 - (c + 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeightHigh_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightHigh c ^ 2 = 1 - (c - 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeight_order {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ≤ contactHeightHigh c := by
  have hlow := contactHeightLow_sq hc hc'
  have hhigh := contactHeightHigh_sq hc hc'
  have hl : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  nlinarith

theorem adjustedContactSpan_continuous (lengths : ℕ → ℝ) :
    Continuous (adjustedContactSpan lengths) := by
  unfold adjustedContactSpan adjustedContactStepX adjustedContactForward
  apply continuous_finsetSum
  intro k _
  split_ifs <;> fun_prop

/-- The low-height endpoint overshoots the desired unperturbed span. -/
theorem adjustedContactSpan_low {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    5 + 4 * c + contactLengthTolerance ≤ adjustedContactSpan lengths (contactHeightLow c) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have h2 := (hf 2 (by norm_num)).1
  have h3 := (hf 3 (by norm_num)).1
  have h5 := (hf 5 (by norm_num)).1
  have h6 := (hf 6 (by norm_num)).1
  have h0 := hl 0 (by norm_num)
  have h1 := hl 1 (by norm_num)
  have h4 := hl 4 (by norm_num)
  have h7 := hl 7 (by norm_num)
  have h8 := hl 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- The high-height endpoint undershoots the desired unperturbed span. -/
theorem adjustedContactSpan_high {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    adjustedContactSpan lengths (contactHeightHigh c) ≤ 5 + 4 * c - contactLengthTolerance := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have h2 := (hf 2 (by norm_num)).2
  have h3 := (hf 3 (by norm_num)).2
  have h5 := (hf 5 (by norm_num)).2
  have h6 := (hf 6 (by norm_num)).2
  have h0 := hl' 0 (by norm_num)
  have h1 := hl' 1 (by norm_num)
  have h4 := hl' 4 (by norm_num)
  have h7 := hl' 7 (by norm_num)
  have h8 := hl' 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- All nine link lengths can be prescribed independently while both
endpoints remain fixed at any allowed span. -/
theorem adjustedContactSpan_exists {c span : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hspan : 5 + 4 * c - contactLengthTolerance ≤ span)
    (hspan' : span ≤ 5 + 4 * c + contactLengthTolerance) :
    ∃ h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c), adjustedContactSpan lengths h = span := by
  have hiv := intermediate_value_Icc' (contactHeight_order hc hc')
    (adjustedContactSpan_continuous lengths).continuousOn
  exact hiv ⟨(adjustedContactSpan_high hc hc' lengths hl hl').trans hspan,
    hspan'.trans (adjustedContactSpan_low hc hc' lengths hl hl')⟩

theorem adjustedContactVertex_end (lengths : ℕ → ℝ) (h : ℝ) :
    adjustedContactVertex lengths h 9 = contactPoint (adjustedContactSpan lengths h) 0 := by
  ext i
  fin_cases i
  · rfl
  · norm_num [adjustedContactVertex, contactPoint, Finset.sum_range_succ, adjustedContactStepY]

/-- The continued path has the prescribed actual Euclidean link lengths. -/
theorem adjustedContact_link_length {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k) {k : ℕ} (hk : k < 9) :
    dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) = lengths k := by
  have hlength : 0 ≤ lengths k := by
    have := hl k hk
    unfold contactLengthTolerance at this
    linarith
  have hlow : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh := contactHeightHigh_sq hc hc'
  have hh0 : 0 ≤ h := hlow.trans hh.1
  have hh2 : h ^ 2 ≤ contactHeightHigh c ^ 2 := by nlinarith [hh.2]
  have hmin := hl k hk
  have hmin2 : (1 - contactLengthTolerance) ^ 2 ≤ lengths k ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hmin)
      (show 0 ≤ lengths k + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ (c - 1 / 1000) ^ 2 := by nlinarith
  have hrad : 0 ≤ lengths k ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hmin2
    nlinarith
  have hroot : adjustedContactForward (lengths k) h ^ 2 = lengths k ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsq : dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) ^ 2 =
      lengths k ^ 2 := by
    unfold adjustedContactVertex
    rw [contactPoint_dist_sq]
    simp only [Finset.sum_range_succ, add_sub_cancel_left]
    unfold adjustedContactStepX adjustedContactStepY
    split_ifs <;> (try omega) <;> nlinarith
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h (k + 1))
    (adjustedContactVertex lengths h k) from dist_nonneg]

end ContinuumCoulomb

end

end OAI
