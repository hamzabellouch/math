import OAI.NumberTheory.DirichletL.Hecke.Euler
import OAI.NumberTheory.DirichletL.Supremum

namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

theorem exists_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hεsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
      (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ beta - ε < s.re := by
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    zeroSet_bddAbove hε hεsmall
  obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hpos, hpole, hz, hlt⟩

theorem beta_le_seven_eighths_of_uniform_margin
    (hbound : 7 / 8 < beta →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < beta - 7 / 8 ∧ 0 < σ ∧
        ∀ (χ : Character) (s : ℂ), 0 < s.re →
          (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s = 0 →
            s.re ≤ beta - Supremum.continuationMargin beta ω σ) :
    beta ≤ 7 / 8 := by
  apply Supremum.seven_eighths_of_uniform_margin_with_sentinel zeroSet_bddAbove
  intro hbeta
  obtain ⟨ω, σ, hω, hωb, hσ, hzeros⟩ := hbound hbeta
  refine ⟨ω, σ, hω, hωb, hσ, ?_⟩
  rintro x ⟨χ, s, hpos, hpole, hz, rfl⟩
  exact hzeros χ s hpos hpole hz

end SevenEighths.HeckeZeroSupremum

end

end OAI
