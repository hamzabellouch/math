import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Pulses

namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

def Rectangle.CollarSeparated {N : ℕ} (R : Fin N → Rectangle) (d : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ y ∈ (R j).carrier,
    ∃ k, (R i).halfWidth k + d ≤ |y k - (R i).center k|

theorem Rectangle.disjoint_of_separated {N : ℕ} {R : Fin N → Rectangle}
    (h : SeparatelySeparated R) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (R i).carrier (R j).carrier := by
  obtain ⟨δ,hδ,hh⟩ := h i j hij
  rw [Set.disjoint_left]
  intro y hi hj
  have hn := hh y hi y hj
  simp only [sub_self, norm_zero] at hn
  exact (not_le_of_gt hδ) hn

theorem Rectangle.exists_coordinate_gap {P Q : Rectangle} (h : Disjoint P.carrier Q.carrier) :
    ∃ k, P.upper k < Q.lower k ∨ Q.upper k < P.lower k := by
  by_contra hn
  push Not at hn
  have hmin (k : Fin 2) : max (P.lower k) (Q.lower k) ≤ min (P.upper k) (Q.upper k) := by
    rcases hn k with ⟨h₁,h₂⟩
    exact max_le (le_min (P.positive k).le h₂) (le_min h₁ (Q.positive k).le)
  have hy : (fun k => ((max (P.lower k) (Q.lower k) : ℚ) : ℝ)) ∈ P.carrier ∩ Q.carrier := by
    constructor
    · intro k
      dsimp only
      constructor
      · exact_mod_cast le_max_left (P.lower k) (Q.lower k)
      · exact_mod_cast (hmin k).trans (min_le_left _ _)
    · intro k
      dsimp only
      constructor
      · exact_mod_cast le_max_right (P.lower k) (Q.lower k)
      · exact_mod_cast (hmin k).trans (min_le_right _ _)
  exact Set.disjoint_left.mp h hy.1 hy.2

theorem Rectangle.collar_of_coordinate_gap {P Q : Rectangle} {d : ℝ} {k : Fin 2}
    (h : (P.upper k : ℝ) + d ≤ Q.lower k ∨ (Q.upper k : ℝ) + d ≤ P.lower k)
    {y : Plane} (hy : y ∈ Q.carrier) : P.halfWidth k + d ≤ |y k - P.center k| := by
  rcases h with h | h
  · apply le_abs.mpr
    left
    have hyk := (hy k).1
    dsimp [Rectangle.halfWidth, Rectangle.center]
    linarith
  · apply le_abs.mpr
    right
    have hyk := (hy k).2
    dsimp [Rectangle.halfWidth, Rectangle.center]
    linarith

theorem Rectangle.exists_rational_collar {N : ℕ} {R : Fin N → Rectangle}
    (h : SeparatelySeparated R) :
    ∃ d : ℚ, 0 < d ∧ d ≤ 1/10 ∧ Rectangle.CollarSeparated R (d : ℝ) := by
  classical
  have hpair (i j : Fin N) : ∃ d : ℚ, 0 < d ∧
      (i ≠ j → ∀ y ∈ (R j).carrier,
        ∃ k, (R i).halfWidth k + (d : ℝ) ≤ |y k - (R i).center k|) := by
    by_cases hij : i = j
    · exact ⟨1, by norm_num, fun hc => (hc hij).elim⟩
    obtain ⟨k,hk⟩ := Rectangle.exists_coordinate_gap (Rectangle.disjoint_of_separated h hij)
    rcases hk with hk | hk
    · refine ⟨(R j).lower k - (R i).upper k, sub_pos.mpr hk, fun _ y hy => ⟨k, ?_⟩⟩
      apply Rectangle.collar_of_coordinate_gap (Or.inl ?_) hy
      push_cast
      ring_nf
      exact le_refl _
    · refine ⟨(R i).lower k - (R j).upper k, sub_pos.mpr hk, fun _ y hy => ⟨k, ?_⟩⟩
      apply Rectangle.collar_of_coordinate_gap (Or.inr ?_) hy
      push_cast
      ring_nf
      exact le_refl _
  choose ds hpos hg using hpair
  let S : Finset ℚ := insert (1/10) (Finset.univ.image (fun ij : Fin N × Fin N => ds ij.1 ij.2))
  have hS : S.Nonempty := ⟨1/10, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, S.min'_le _ (Finset.mem_insert_self _ _), ?_⟩
  · rw [Finset.lt_min'_iff]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · norm_num
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hq
    exact hpos i j
  · intro i j hij y hy
    obtain ⟨k,hk⟩ := hg i j hij y hy
    refine ⟨k, le_trans ?_ hk⟩
    apply add_le_add (le_refl _)
    exact_mod_cast S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ (i,j))))

theorem Rectangle.CollarSeparated.mono {N : ℕ} {R : Fin N → Rectangle} {d e : ℝ}
    (h : Rectangle.CollarSeparated R d) (he : e ≤ d) : Rectangle.CollarSeparated R e := by
  intro i j hij y hy
  obtain ⟨k,hk⟩ := h i j hij y hy
  exact ⟨k, (add_le_add (le_refl _) he).trans hk⟩

theorem SheetData.exists_rational_collar {N : ℕ} (D : SheetData N) :
    ∃ d : ℚ, 0 < d ∧ d ≤ 1/10 ∧ Rectangle.CollarSeparated D.source (d : ℝ) ∧
      Rectangle.CollarSeparated D.target (d : ℝ) := by
  obtain ⟨a,ha,ha',hs⟩ := Rectangle.exists_rational_collar D.source_separated
  obtain ⟨b,hb,_,ht⟩ := Rectangle.exists_rational_collar D.target_separated
  refine ⟨min a b, lt_min ha hb, (min_le_left _ _).trans ha', hs.mono ?_, ht.mono ?_⟩
  · exact_mod_cast min_le_left a b
  · exact_mod_cast min_le_right a b

theorem Rectangle.center_bounds (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2) :
    2 ≤ R.center j ∧ R.center j ≤ 3 := by
  have hl : (2:ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j:ℝ) ≤ 3 := by exact_mod_cast (hR j).2
  have hw : (R.lower j:ℝ) ≤ R.upper j := by exact_mod_cast (R.positive j).le
  dsimp [Rectangle.center]
  constructor <;> linarith

theorem Rectangle.point_bounds (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) (j : Fin 2) : 2 ≤ y j ∧ y j ≤ 3 := by
  have hl : (2:ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j:ℝ) ≤ 3 := by exact_mod_cast (hR j).2
  exact ⟨hl.trans (hy j).1, (hy j).2.trans hu⟩

structure Collar where
  size : ℝ
  positive : 0 < size
  small : size ≤ 1/10

variable (d : Collar)

def lifted (s z : ℝ) (y : Plane) : Space := ![y 0 + s, y 1, z]

def verticalPulse (R : Rectangle) (hR : R.inCodingSquare) (s : ℝ) : StationaryPulse :=
  StationaryPulse.tensor 2
    ![Cprofile (R.halfWidth 0) d.size (R.center 0+s),
      fun x => Cprofile (R.halfWidth 1) d.size (R.center 1) x -
        Cprofile (R.halfWidth 1) d.size (R.center 1+4) x, fun _ => 1]
    (by intro j; fin_cases j
        · exact Cprofile_contDiff _ _ d.positive
        · exact (Cprofile_contDiff _ _ d.positive).sub (Cprofile_contDiff _ _ d.positive)
        · exact contDiff_const)
    (by intro j; fin_cases j
        · exact Cprofile_periodic _ _ _
        · exact (Cprofile_periodic _ _ _).sub (Cprofile_periodic _ _ _)
        · exact fun _ => rfl)
    (fun _ => rfl) 1
    (by
      apply Cprofile_corrected_integral_zero d.positive <;>
        have hw := R.halfWidth_le_half hR 1 <;>
        have hc := R.center_bounds hR 1 <;>
        linarith [d.small])

theorem verticalPulse_field (R : Rectangle) (hR : R.inCodingSquare) (s : ℝ) (x : Space) :
    (verticalPulse d R hR s).field x =
      (Cprofile (R.halfWidth 0) d.size (R.center 0+s) (x 0) *
        (Cprofile (R.halfWidth 1) d.size (R.center 1) (x 1) -
          Cprofile (R.halfWidth 1) d.size (R.center 1+4) (x 1))) • basis 2 := by
  simp [verticalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem rect_support_chart (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) :
    R.halfWidth j + d.size ≤ R.center j + s ∧
      R.center j + s + (R.halfWidth j + d.size) ≤ 10 := by
  have hw := R.halfWidth_le_half hR j
  have hc := R.center_bounds hR j
  constructor <;> linarith [d.small, hs.1, hs.2]

theorem correction_off (R : Rectangle) (hR : R.inCodingSquare)
    {y : ℝ} (hy : y ∈ Set.Icc 2 3) :
    Cprofile (R.halfWidth 1) d.size (R.center 1+4) y = 0 := by
  have hc := rect_support_chart d R hR 1 (s := 4) (by norm_num)
  apply Cprofile_zero_on_chart d.positive hc.1 hc.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
  apply le_abs.mpr
  right
  linarith [R.halfWidth_le_half hR 1, (R.center_bounds hR 1).1, d.small, hy.2]

theorem rect_profile_one (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) :
    Cprofile (R.halfWidth j) d.size (R.center j+s) (y j+s) = 1 := by
  have hc := rect_support_chart d R hR j hs
  apply Cprofile_one d.positive hc.1 hc.2
  · have hb := R.point_bounds hR hy j
    constructor <;> linarith [hs.1, hs.2, hb.1, hb.2]
  · have hb := (R.mem_iff_abs y).mp hy j
    have he : y j + s - (R.center j+s) = y j - R.center j := by ring
    rw [he]
    linarith [d.positive]

theorem verticalPulse_own (R : Rectangle) (hR : R.inCodingSquare)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) (z : ℝ) :
    (verticalPulse d R hR s).field (lifted s z y) = basis 2 := by
  rw [verticalPulse_field]
  have h₀ := rect_profile_one d R hR 0 hs hy
  have h₁ := rect_profile_one d R hR 1 (s := 0) (by norm_num) hy
  simp only [add_zero] at h₁
  simp only [lifted, Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁,
    correction_off d R hR (R.point_bounds hR hy 1), sub_zero, mul_one, one_smul]

theorem rect_profile_gap_zero (P Q : Rectangle) (hP : P.inCodingSquare)
    (hQ : Q.inCodingSquare) (k : Fin 2) {s : ℝ} (hs : s ∈ Set.Icc 0 4)
    {y : Plane} (hy : y ∈ Q.carrier)
    (hgap : P.halfWidth k + d.size ≤ |y k-P.center k|) :
    Cprofile (P.halfWidth k) d.size (P.center k+s) (y k+s) = 0 := by
  have hc := rect_support_chart d P hP k hs
  apply Cprofile_zero_on_chart d.positive hc.1 hc.2
  · have hb := Q.point_bounds hQ hy k
    constructor <;> linarith [hs.1, hs.2, hb.1, hb.2]
  · have he : y k+s-(P.center k+s) = y k-P.center k := by ring
    rw [he]
    exact hgap

theorem verticalPulse_off_same {N : ℕ} (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hsep : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {s : ℝ} (hs : s ∈ Set.Icc 0 4)
    {y : Plane} (hy : y ∈ (R j).carrier) (z : ℝ) :
    (verticalPulse d (R i) (hR i) s).field (lifted s z y) = 0 := by
  obtain ⟨k,hk⟩ := hsep i j hij y hy
  have hc := correction_off d (R i) (hR i) ((R j).point_bounds (hR j) hy 1)
  rw [verticalPulse_field]
  fin_cases k
  · have hz := rect_profile_gap_zero d (R i) (R j) (hR i) (hR j) 0 hs hy hk
    simp [lifted, hz]
  · have hz := rect_profile_gap_zero d (R i) (R j) (hR i) (hR j) 1 (s := 0) (by norm_num) hy hk
    simp only [add_zero] at hz
    simp [lifted, hc, hz]

theorem verticalPulse_off_far (P Q : Rectangle) (hP : P.inCodingSquare)
    (hQ : Q.inCodingSquare) {s t : ℝ} (hs : s ∈ Set.Icc 0 4)
    (ht : t ∈ Set.Icc 0 4) (hst : 4 ≤ |t-s|) {y : Plane} (hy : y ∈ Q.carrier) (z : ℝ) :
    (verticalPulse d P hP s).field (lifted t z y) = 0 := by
  have hc := rect_support_chart d P hP 0 hs
  have hz : Cprofile (P.halfWidth 0) d.size (P.center 0+s) (y 0+t) = 0 := by
    apply Cprofile_zero_on_chart d.positive hc.1 hc.2
    · have hb := Q.point_bounds hQ hy 0
      constructor <;> linarith [ht.1, ht.2, hb.1, hb.2]
    · rcases le_abs.mp hst with hf | hf
      · apply le_abs.mpr (Or.inl ?_)
        linarith [(Q.point_bounds hQ hy 0).1, (P.center_bounds hP 0).2,
          P.halfWidth_le_half hP 0, d.small]
      · apply le_abs.mpr (Or.inr ?_)
        linarith [(Q.point_bounds hQ hy 0).2, (P.center_bounds hP 0).1,
          P.halfWidth_le_half hP 0, d.small]
  simp [verticalPulse_field, lifted, hz]

def horizontalPulse (j : Fin 2) : StationaryPulse :=
  StationaryPulse.tensor j.castSucc
    ![fun _ => 1, fun _ => 1, fun z => Cprofile 0 d.size 5 z - Cprofile 0 d.size 8 z]
    (by intro k; fin_cases k
        · exact contDiff_const
        · exact contDiff_const
        · exact (Cprofile_contDiff _ _ d.positive).sub (Cprofile_contDiff _ _ d.positive))
    (by intro k; fin_cases k
        · exact fun _ => rfl
        · exact fun _ => rfl
        · exact (Cprofile_periodic _ _ _).sub (Cprofile_periodic _ _ _))
    (by intro s; fin_cases j <;> rfl) 2
    (by apply Cprofile_corrected_integral_zero d.positive <;> linarith [d.small])

theorem horizontalPulse_field (j : Fin 2) (x : Space) :
    (horizontalPulse d j).field x =
      (Cprofile 0 d.size 5 (x 2) - Cprofile 0 d.size 8 (x 2)) • basis j.castSucc := by
  simp [horizontalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem horizontalPulse_on (j : Fin 2) {x : Space} (hx : x 2 = 5) :
    (horizontalPulse d j).field x = basis j.castSucc := by
  have h₅ : Cprofile 0 d.size 5 5 = 1 := by
    apply Cprofile_one d.positive <;> norm_num <;> linarith [d.small, d.positive]
  have h₈ : Cprofile 0 d.size 8 5 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  simp only [horizontalPulse_field, hx, h₅, h₈, sub_zero, one_smul]

theorem horizontalPulse_off (j : Fin 2) {x : Space} (hx : x 2 = 2) :
    (horizontalPulse d j).field x = 0 := by
  have h₅ : Cprofile 0 d.size 5 2 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  have h₈ : Cprofile 0 d.size 8 2 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  simp only [horizontalPulse_field, hx, h₅, h₈, sub_self, zero_smul]

@[simp] theorem StationaryPulse.scale_field (c : ℝ) (p : StationaryPulse) (x : Space) :
    (p.scale c).field x = c • p.field x := rfl

def travelProgram (δ : Plane) : List StationaryPulse :=
  [(horizontalPulse d 0).scale (δ 0), (horizontalPulse d 1).scale (δ 1)]

theorem travelProgram_on (δ : Plane) (x y : ℝ) :
    runProgram (travelProgram d δ) ![x,y,5] = ![x+δ 0,y+δ 1,5] := by
  have h₀ : ((horizontalPulse d 0).scale (δ 0)).apply ![x,y,5] = ![x+δ 0,y,5] := by
    simp only [StationaryPulse.apply, StationaryPulse.scale_field,
      horizontalPulse_on d 0 (by rfl : (![x,y,5] : Space) 2 = 5)]
    ext i; fin_cases i <;> simp [basis]
  have h₁ : ((horizontalPulse d 1).scale (δ 1)).apply ![x+δ 0,y,5] = ![x+δ 0,y+δ 1,5] := by
    simp only [StationaryPulse.apply, StationaryPulse.scale_field,
      horizontalPulse_on d 1 (by rfl : (![x+δ 0,y,5] : Space) 2 = 5)]
    ext i; fin_cases i <;> simp [basis]
  change ((horizontalPulse d 1).scale (δ 1)).apply
    (((horizontalPulse d 0).scale (δ 0)).apply ![x,y,5]) = _
  rw [h₀, h₁]

theorem travelProgram_off (δ : Plane) (x : Space) (hx : x 2 = 2) :
    runProgram (travelProgram d δ) x = x := by
  apply runProgram_fixed
  intro p hp
  simp only [travelProgram, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [horizontalPulse_off d _ hx]

end Solenoidal
end
end


end OAI
