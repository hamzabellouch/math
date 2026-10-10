import OAI.NumberTheory.Ostmann.Construction.SeparatedPrimeBands

namespace OAI

/-! # The three selected prime bands give all character separation parameters -/
namespace Ostmann

noncomputable def characterBandPoint (α β : ℝ) (q i : ℕ) : ℝ :=
  α + i * ((β - α) / q)

theorem characterBandPoint_strictMono (α β : ℝ) (q : ℕ) (hαβ : α < β) (hq : 0 < q) :
    StrictMono (characterBandPoint α β q) := by
  intro i j hij
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  exact add_lt_add_right (mul_lt_mul_of_pos_right hijR (div_pos (sub_pos.mpr hαβ) hqR)) α

theorem characterBandPoint_bounds (α β : ℝ) (q i : ℕ)
    (hαβ : α < β) (hq : 0 < q) (hi : i ≤ q) :
    α ≤ characterBandPoint α β q i ∧ characterBandPoint α β q i ≤ β := by
  have hmono := (characterBandPoint_strictMono α β q hαβ hq).monotone
  have hzero : characterBandPoint α β q 0 = α := by simp [characterBandPoint]
  have hlast : characterBandPoint α β q q = β := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    unfold characterBandPoint
    field_simp
    ring
  exact ⟨by simpa only [hzero] using hmono (Nat.zero_le i),
    by simpa only [hlast] using hmono hi⟩

/-- Midpoints of the unused partition gaps satisfy the strict margins required
by both the anchor and nonanchor energy comparisons. -/
theorem character_three_band_margins (α β : ℝ) (q : ℕ) (hα : 0 < α) (hαβ : α < β)
    (hq : 0 < q) (i j k : Fin q) (hij : i.val + 1 < j.val) (hjk : j.val + 1 < k.val) :
    let γs := characterBandPoint α β q (i.val + 1)
    let νw := characterBandPoint α β q j.val
    let γw := characterBandPoint α β q (j.val + 1)
    let νa := characterBandPoint α β q k.val
    let βw := (γs + νw) / 2
    let βa := (γw + νa) / 2
    0 < α / 2 ∧ α / 2 < βw ∧ γs < βw ∧ βw < νw ∧
      α / 2 < βa ∧ γw < βa ∧ βa < νa ∧
      0 ≤ γw ∧ γw ≤ β + 1 ∧ νa < β + 1 := by
  intro γs νw γw νa βw βa
  have hmono := characterBandPoint_strictMono α β q hαβ hq
  have hsmall : γs < νw := hmono hij
  have hlarge : γw < νa := hmono hjk
  have hγs := (characterBandPoint_bounds α β q (i.val + 1) hαβ hq (by omega)).1
  have hγw := characterBandPoint_bounds α β q (j.val + 1) hαβ hq (by omega)
  have hνa := (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).2
  dsimp only [βw, βa]
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith [hγw.1],
    by linarith [hγw.2], by linarith⟩

end Ostmann

end OAI
