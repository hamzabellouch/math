import OAI.MeasureTheory.Falconer.Recursion.ProfileRoundContact

namespace OAI

/-! # The three contact inequalities at actual integer dyadic depths -/

namespace Falconer
open Set
open scoped NNReal

theorem floor_depth_ratio_bounds {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (hN : 0 < N) :
    0 ≤ (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ∧
    (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ A ∧
    A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ 1/(N:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlo := Nat.floor_le (mul_nonneg hA hNp.le)
  have hhi := Nat.lt_floor_add_one (A*(N:ℝ))
  refine ⟨by positivity,(div_le_iff₀ hNp).mpr hlo,?_⟩
  apply (le_div_iff₀ hNp).mpr
  have he : (A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ))*(N:ℝ) =
      A*(N:ℝ)-(Nat.floor (A*(N:ℝ)):ℝ) := by field_simp
  rw [he]
  linarith

theorem rounded_profile_contact {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {A B q t E : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hfirst : ∀ w ∈ Icc 0 A, q*w-E ≤ f w)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A)-E ≤ f w-f A)
    (hlast : ∀ w ∈ Icc B 1, q*(w-B)-E ≤ f w-f B)
    {N : ℕ} (hN : 0 < N) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-E ≤ f ((j:ℝ)/N)) ∧
    (∀ j : ℕ, a ≤ j → j ≤ b →
      t*(j-a:ℕ)/N-E-((K:ℝ)+t)/N ≤ f ((j:ℝ)/N)-f ((a:ℝ)/N)) ∧
    (∀ j : ℕ, b ≤ j → j ≤ N →
      q*(j-b:ℕ)/N-E-((K:ℝ)+q)/N ≤ f ((j:ℝ)/N)-f ((b:ℝ)/N)) := by
  dsimp only
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have ha := floor_depth_ratio_bounds hA hN
  have hb := floor_depth_ratio_bounds (hA.trans hAB) hN
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hma := profile_contact_move_left hLip ha.1 ha.2.1 hAB hB ht ha.2.2 hmiddle
  have hlb := profile_contact_move_left hLip hb.1 hb.2.1 hB (le_refl (1:ℝ)) hq hb.2.2 hlast
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hjA : (j:ℝ)/N ≤ A := (div_le_div_of_nonneg_right (by exact_mod_cast hj) hNp.le).trans ha.2.1
    simpa only [mul_div_assoc] using hfirst ((j:ℝ)/N) ⟨by positivity,hjA⟩
  · intro j haj hjb
    have hlo : (a:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast haj) hNp.le
    have hhi : (j:ℝ)/N ≤ B := (div_le_div_of_nonneg_right (by exact_mod_cast hjb) hNp.le).trans hb.2.1
    have hh := hma ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub haj]
    convert hh using 1
    ring
  · intro j hbj hjN
    have hlo : (b:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast hbj) hNp.le
    have hhi : (j:ℝ)/N ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hjN)
    have hh := hlb ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub hbj]
    convert hh using 1
    ring

end Falconer

end OAI
