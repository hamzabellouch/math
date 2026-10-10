import OAI.NumberTheory.Jacobsthal.Partitions.LineCoordinateCounts

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosConvexGraph

theorem spacing_implies_height (N S d : ℝ) (hN : 2 ≤ N) (hd : 0 < d)
    (hcount : N ≤ S/d+1) : d ≤ 2*S/N := by
  have hstep : (N-1)*d ≤ S := (le_div_iff₀ hd).mp (by linarith)
  have hNp : 0 < N := by linarith
  apply (le_div_iff₀ hNp).mpr
  nlinarith

theorem PrimitiveIntegerLine.height_bounds (l : PrimitiveIntegerLine)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S) (hN : 2 ≤ X.card)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (l.denominator : ℝ) ≤ 2*S/(X.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(X.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(X.card : ℝ) := by
  have hNR : (2 : ℝ) ≤ X.card := by exact_mod_cast hN
  have hNp : (0 : ℝ) < X.card := by linarith
  have hD : (l.denominator : ℝ) ≤ 2*S/(X.card : ℝ) :=
    spacing_implies_height _ _ _ hNR (by exact_mod_cast l.denominator_pos)
      (l.denominator_point_count X S hS hinj hbox hline)
  have hA : |(l.slope : ℝ)| ≤ 2*S/(X.card : ℝ) := by
    by_cases ha : l.slope = 0
    · simp only [ha,Int.cast_zero,abs_zero]
      positivity
    · have hh := spacing_implies_height _ _ _ hNR
        (show (0 : ℝ) < l.slope.natAbs by exact_mod_cast Int.natAbs_pos.mpr ha)
        (l.slope_point_count ha X S hS hbox hline)
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  have he : (l.intercept : ℝ) = (l.denominator : ℝ)*(p.2 : ℝ)-(l.slope : ℝ)*(p.1 : ℝ) := by
    have hh : l.intercept = (l.denominator : ℤ)*p.2-l.slope*p.1 := by
      have hl := hline p hp
      unfold Contains at hl
      linarith
    exact_mod_cast hh
  have hb := hbox p hp
  have hB : |(l.intercept : ℝ)| ≤ 4*S^2/(X.card : ℝ) := by
    calc
      |(l.intercept : ℝ)| ≤ |(l.denominator : ℝ)*(p.2 : ℝ)|+|(l.slope : ℝ)*(p.1 : ℝ)| := by
        rw [he]
        exact abs_sub _ _
      _ = (l.denominator : ℝ)*(p.2 : ℝ)+|(l.slope : ℝ)| *(p.1 : ℝ) := by
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg hb.2.1,
          abs_of_nonneg hb.1.1]
      _ ≤ (2*S/(X.card : ℝ))*S+(2*S/(X.card : ℝ))*S := add_le_add
        (mul_le_mul hD hb.2.2 hb.2.1 (by positivity))
        (mul_le_mul hA hb.1.2 hb.1.1 (by positivity))
      _ = 4*S^2/(X.card : ℝ) := by ring
  exact ⟨hD,hA,hB⟩

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph

theorem exists_rich_line_with_heights (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (F : MV ℂ) (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)),
      Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      Y = X ∩ complexSquarePoints F S ∧ Y ⊆ X ∧ M < (Y.card : ℝ) ∧
      (∀ r ∈ Y, l.Contains r) ∧
      (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  classical
  obtain ⟨F,l,hF,hFP,hdeg,hcount,hline⟩ := exists_rich_primitive_line P hP D hD S hS X hX hinj M hM hlarge
  let Y := X ∩ complexSquarePoints F S
  have hsub : Y ⊆ X := Finset.inter_subset_left
  have htwo : 2 ≤ Y.card := by
    have hh : (1 : ℝ) < Y.card := lt_of_le_of_lt hM hcount
    have hh' : 1 < Y.card := by exact_mod_cast hh
    omega
  have hbox : ∀ r ∈ Y, InSquare S r := fun r hr =>
    ((mem_complexSquarePoints F S r).mp (Finset.mem_inter.mp hr).2).1
  have hxin : Set.InjOn Prod.fst (Y : Set (ℤ × ℤ)) :=
    fun _ hp _ hq he => hinj (hsub hp) (hsub hq) he
  obtain ⟨hden,hslope,hinter⟩ := l.height_bounds Y S hS htwo hxin hbox hline
  exact ⟨F,l,Y,hF,hFP,hdeg,rfl,hsub,hcount,hline,hden,hslope,hinter⟩

end ErdosRichLine

end

end Erdos970

end OAI
