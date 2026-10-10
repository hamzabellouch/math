import OAI.Combinatorics.ContingencyTables.Machines.FractionAcceptanceProgram
import OAI.Combinatorics.ContingencyTables.Rooted.ForestScaledPenalty

namespace OAI

/-! # Exact binary arithmetic for a forest interval penalty

A signed affine numerator is stored as a difference of two naturals.
Its distance outside the interval [0,1] is a nonnegative fraction with
the same denominator; no signed rational comparison is required.
-/

namespace ContingencyTables.RationalIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := (ℕ×ℕ)×ℕ

def numerator (z : Input) : ℕ := (z.1.2-z.1.1)+(z.1.1-(z.1.2+z.2))

def numeratorRealizer : Realizer numerator := by
  let P : Realizer (fun z : Input => z.1.1) := composition first first
  let N : Realizer (fun z : Input => z.1.2) := composition first second
  let D : Realizer (fun z : Input => z.2) := second
  exact composition (pair (composition (pair N P) subtract)
    (composition (pair P (composition (pair N D) add)) subtract)) add

lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer
  have hp := polynomial_composition
    (polynomial_first (A := ℕ×ℕ) (B := ℕ)) polynomial_first
  have hn := polynomial_composition
    (polynomial_first (A := ℕ×ℕ) (B := ℕ)) polynomial_second
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hn hp) polynomial_subtract)
    (polynomial_composition (polynomial_pair hp
      (polynomial_composition (polynomial_pair hn polynomial_second) polynomial_add))
      polynomial_subtract)) polynomial_add

def intervalCode (z : Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator z,z.2)

def intervalCodeRealizer : Realizer intervalCode :=
  composition (f := fun z : Input => (numerator z,z.2)) (g := TreeFraction.normalize)
    (pair numeratorRealizer second) TreeFraction.normalizeRealizer

theorem polynomial_intervalCode : PolynomialTime intervalCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_second)
    TreeFraction.polynomial_normalize

lemma intervalCode_denominator (z : Input) : 0<(intervalCode z).2 :=
  TreeFraction.normalize_den_pos _

noncomputable section

/-- Exact agreement with the interval cost in the forest density. The
only side condition is the strictly positive tree capacity denominator. -/
theorem intervalCode_value (p n d : ℕ) (hd : 0<d) :
    TreeFraction.val (intervalCode ((p,n),d))=
      max 0 (max (-(((p:ℚ)-n)/d)) (((p:ℚ)-n)/d-1)) := by
  rw [intervalCode,TreeFraction.normalize_val]
  change (((n-p)+(p-(n+d)):ℕ):ℚ)/d=_
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  let x : ℚ := ((p:ℚ)-n)/d
  change (((n-p)+(p-(n+d)):ℕ):ℚ)/d=max 0 (max (-x) (x-1))
  by_cases hpn : p≤n
  · have hx : x≤0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (by exact_mod_cast hpn)) hdq.le
    have hsub : p≤n+d := by omega
    simp only [Nat.sub_eq_zero_of_le hsub,Nat.add_zero,Nat.cast_sub hpn,
      max_eq_left (show x-1≤-x by linarith),max_eq_right (neg_nonneg.mpr hx)]
    dsimp only [x]
    ring
  · have hnp : n≤p := by omega
    have hx : 0≤x := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hnp)) hdq.le
    by_cases hpd : p≤n+d
    · have hx1 : x≤1 := (div_le_one hdq).mpr (by
        have hh : (p:ℚ)≤n+d := by exact_mod_cast hpd
        linarith)
      simp only [Nat.sub_eq_zero_of_le hnp,Nat.sub_eq_zero_of_le hpd,Nat.zero_add,
        Nat.cast_zero,zero_div]
      symm
      exact max_eq_left (max_le (neg_nonpos.mpr hx) (by linarith))
    · have hdp : n+d≤p := by omega
      have hx1 : 1≤x := (le_div_iff₀ hdq).mpr (by
        have hh : (n:ℚ)+d≤p := by exact_mod_cast hdp
        linarith)
      simp only [Nat.sub_eq_zero_of_le hnp,Nat.zero_add,Nat.cast_sub hdp,Nat.cast_add,
        max_eq_right (show -x≤x-1 by linarith),max_eq_right (sub_nonneg.mpr hx1)]
      dsimp only [x]
      field_simp [hdq.ne']
      ring

end
end ContingencyTables.RationalIntervalProgram

end OAI
