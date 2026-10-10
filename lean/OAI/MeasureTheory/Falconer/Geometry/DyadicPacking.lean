import OAI.MeasureTheory.Falconer.Measures.DyadicMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Finset.Union

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

def dyadicPaths : ℕ → Finset (List (Bool × Bool))
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion fun a : Bool × Bool =>
      (dyadicPaths n).image (List.cons a)

@[simp] theorem mem_dyadicPaths (n : ℕ) (p : List (Bool × Bool)) :
    p ∈ dyadicPaths n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [dyadicPaths]
  | succ n ih =>
    cases p with
    | nil => simp [dyadicPaths]
    | cons a p => simp [dyadicPaths, ih]

theorem DyadicSquare.descendant_side (Q : DyadicSquare) (p : List (Bool × Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons a p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem DyadicSquare.descendants_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side)
    {p q : List (Bool × Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).carrier (Q.descendant q).carrier := by
  induction p generalizing Q q with
  | nil =>
    have : q = [] := by cases q <;> simp_all
    exact (hne this.symm).elim
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      by_cases hab : a = b
      · subst b
        exact ih _ (Q.child_side_pos hQ a.1 a.2) (by simpa using hlen)
          (by intro he; exact hne (he ▸ rfl))
      · exact (Q.children_disjoint hab).mono
          ((Q.child a.1 a.2).descendant_subset (Q.child_side_pos hQ a.1 a.2) p)
          ((Q.child b.1 b.2).descendant_subset (Q.child_side_pos hQ b.1 b.2) q)

theorem DyadicSquare.mem_descendant_at_depth (Q : DyadicSquare) (n : ℕ)
    {z : Plane} (hz : z ∈ Q.carrier) :
    ∃ p ∈ dyadicPaths n, z ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[],by simp, hz⟩
  | succ n ih =>
    have step (i j : Bool) (hz : z ∈ (Q.child i j).carrier) :
        ∃ p ∈ dyadicPaths (n+1), z ∈ (Q.descendant p).carrier := by
      obtain ⟨p,hp,hz⟩ := ih _ hz
      exact ⟨(i,j) :: p,by simpa using hp,hz⟩
    rw [Q.cover_children] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact step false false hz
    · exact step false true hz
    · exact step true false hz
    · exact step true true hz

def DyadicSquare.box (Q : DyadicSquare) : Set (ℝ × ℝ) :=
  Ico Q.x (Q.x+Q.side) ×ˢ Ico Q.y (Q.y+Q.side)

def pairToPlane (z : ℝ × ℝ) : Plane := WithLp.toLp 2 ![z.1,z.2]

@[simp] theorem pairToPlane_mem (Q : DyadicSquare) (z : ℝ × ℝ) :
    pairToPlane z ∈ Q.carrier ↔ z ∈ Q.box := by
  simp only [pairToPlane, DyadicSquare.carrier, DyadicSquare.box,
    mem_ofPred_eq, mem_prod, mem_Ico,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

theorem DyadicSquare.box_measurable (Q : DyadicSquare) : MeasurableSet Q.box :=
  measurableSet_Ico.prod measurableSet_Ico

theorem DyadicSquare.box_area (Q : DyadicSquare) :
    (volume.prod volume) Q.box = ENNReal.ofReal Q.side * ENNReal.ofReal Q.side := by
  simp [box, Measure.prod_prod, Real.volume_Ico]

theorem DyadicSquare.boxes_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side)
    {p q : List (Bool × Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).box (Q.descendant q).box := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ hlen hne)
    ((pairToPlane_mem _ _).mpr hp) ((pairToPlane_mem _ _).mpr hq)

theorem plane_coordinate_dist_le (z x : Plane) (i : Fin 2) :
    |z i - x i| ≤ dist z x := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le z x i

theorem box_subset_of_meets_ball (Q : DyadicSquare) (x : Plane) {r w : ℝ}
    (hside : Q.side = w) (hr : r ≤ w)
    (hmeet : (Q.carrier ∩ ball x r).Nonempty) :
    Q.box ⊆ Icc (x 0-2*w) (x 0+2*w) ×ˢ Icc (x 1-2*w) (x 1+2*w) := by
  obtain ⟨z,hz,hball⟩ := hmeet
  have h0 := (plane_coordinate_dist_le z x 0).trans_lt hball
  have h1 := (plane_coordinate_dist_le z x 1).trans_lt hball
  have hx0 := abs_lt.mp h0
  have hx1 := abs_lt.mp h1
  intro u hu
  simp only [DyadicSquare.box, mem_prod, mem_Ico] at hu
  simp only [DyadicSquare.carrier, mem_ofPred_eq] at hz
  simp only [mem_prod, mem_Icc]
  rw [hside] at hz hu
  constructor <;> constructor <;> linarith [hu.1.1,hu.1.2,hu.2.1,hu.2.2,
    hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,hx0.1,hx0.2,hx1.1,hx1.2]

noncomputable def cellsMeeting (Q : DyadicSquare) (n : ℕ) (x : Plane) (r : ℝ) :
    Finset (List (Bool × Bool)) := by
  classical
  exact (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty

theorem dyadic_ball_card_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) (x : Plane) {r : ℝ} (hr : r ≤ Q.side/(2 : ℝ)^n) :
    (cellsMeeting Q n x r).card ≤ 16 := by
  classical
  let S := (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty
  let w := Q.side/(2 : ℝ)^n
  have hw : 0 < w := by dsimp [w]; positivity
  have hlen {path : List (Bool × Bool)} (hp : path ∈ S) : path.length = n :=
    (mem_dyadicPaths n path).mp (Finset.mem_filter.mp hp).1
  have hside {path : List (Bool × Bool)} (hp : path ∈ S) :
      (Q.descendant path).side = w := by
    rw [Q.descendant_side, hlen hp]
  have hdis : PairwiseDisjoint (S : Set (List (Bool × Bool)))
      (fun p => (Q.descendant p).box) := by
    intro p hp q hq hpq
    exact Q.boxes_disjoint hQ ((hlen hp).trans (hlen hq).symm) hpq
  have harea : (∑ p ∈ S, ENNReal.ofReal w * ENNReal.ofReal w) ≤
      ENNReal.ofReal (4*w) * ENNReal.ofReal (4*w) := by
    calc
      _ = ∑ p ∈ S, (volume.prod volume) (Q.descendant p).box := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [DyadicSquare.box_area, hside hp]
      _ = (volume.prod volume) (⋃ p ∈ S, (Q.descendant p).box) :=
        (measure_biUnion_finset hdis (fun p _ => (Q.descendant p).box_measurable)).symm
      _ ≤ (volume.prod volume)
          (Icc (x 0-2*w) (x 0+2*w) ×ˢ Icc (x 1-2*w) (x 1+2*w)) := by
        apply measure_mono
        intro u hu
        obtain ⟨p,hp,hu⟩ := mem_iUnion₂.mp hu
        exact box_subset_of_meets_ball _ x (hside hp) hr
          (Finset.mem_filter.mp hp).2 hu
      _ = _ := by
        rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
        congr 2 <;> ring
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) harea
  simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hw.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*w)] at hreal
  have hcard : (S.card : ℝ) ≤ 16 := by
    by_contra h
    have hpos := mul_pos (show 0 < (S.card : ℝ)-16 by linarith) (mul_pos hw hw)
    nlinarith [hreal]

  exact_mod_cast hcard

theorem dyadic_ball_measure_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) (hcarry : μ Q.carrierᶜ = 0)
    (s C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hb : ∀ p : List (Bool × Bool), p.length = n →
      μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(Q.descendant p).side^s))
    (x : Plane) {r : ℝ} (hr : r ≤ Q.side/(2 : ℝ)^n) :
    μ (ball x r) ≤ ENNReal.ofReal (16*C*(Q.side/(2 : ℝ)^n)^s) := by
  classical
  let S := (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty
  have hcover : ball x r ⊆ (⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ := by
    intro z hz
    by_cases hQz : z ∈ Q.carrier
    · obtain ⟨p,hp,hzp⟩ := Q.mem_descendant_at_depth n hQz
      exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,⟨z,hzp,hz⟩⟩,hzp⟩)
    · exact Or.inr hQz
  calc
    μ (ball x r) ≤ μ ((⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ) := measure_mono hcover
    _ ≤ μ (⋃ p ∈ S, (Q.descendant p).carrier) + μ Q.carrierᶜ := measure_union_le _ _
    _ = μ (⋃ p ∈ S, (Q.descendant p).carrier) := by rw [hcarry, add_zero]
    _ ≤ ∑ p ∈ S, μ (Q.descendant p).carrier := measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ S, ENNReal.ofReal (C*(Q.side/(2 : ℝ)^n)^s) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := (mem_dyadicPaths n p).mp (Finset.mem_filter.mp hp).1
      simpa only [Q.descendant_side, hl] using hb p hl
    _ ≤ (16 : ℝ≥0∞) * ENNReal.ofReal (C*(Q.side/(2 : ℝ)^n)^s) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast dyadic_ball_card_le Q hQ n x hr) _
    _ = _ := by
      rw [show (16 : ℝ≥0∞) = ENNReal.ofReal (16 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul' (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))]
      congr 1
      ring

end PlanarFalconer

end OAI
