import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyAgreement
import OAI.Combinatorics.BalancedRyser.Selection.SelectionScales

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

def Parameters.occupancyDecay (p : Parameters) : ℝ :=
  p.c₀ ^ 2 / (96 * ((1 + p.Bstar) / Real.exp (-6 * p.Bstar)) ^ 2)

theorem Parameters.occupancyDecay_pos (p : Parameters) (hp : p.Admissible) :
    0 < p.occupancyDecay := by
  have hc := hp.1
  have hc₀ := hp.2.2.1
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  unfold Parameters.occupancyDecay
  positivity

theorem surviving_source_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (hcard : p.c₀ * q ≤ (T.card : ℝ))
    (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧
      ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} ≤ 2 * Real.exp (-p.occupancyDecay * q) := by
  have hc := hp.1
  have hC := hp.2.1
  have hc₀ := hp.2.2.1
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hP : 0 < p.Pstar := by unfold Parameters.Pstar; positivity
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  have hfactor : 0 < 1 - p.Bstar / q := by
    have hhalf : p.Bstar / q ≤ 1 / 2 := (div_le_iff₀ hqR).2 (by linarith)
    linarith
  have hd : 0 < Real.exp (-6 * p.Bstar) := Real.exp_pos _
  have hscale : ∀ j < 3 * q, p.smin ≤ p.sizeScale q j := by
    intro j hj
    exact (SelectionScales.domain_bounds hP.le hq hPq hj.le).1
  have hdenom : ∀ j ≤ 3 * q, Real.exp (-6 * p.Bstar) ≤ (1 - p.Bstar / q) ^ j := by
    intro j hj
    exact (SelectionScales.domain_bounds hB.le hq hBq hj).1
  have hu : 0 < p.c₀ * (q : ℝ) / 2 := by positivity
  have hub : p.c₀ * (q : ℝ) / 2 ≤ (T.card : ℝ) := by linarith
  have hb := surviving_occupancy_lower_tail p q (3 * q) G hc hq (by omega)
    hscale hfactor A index line hline l T hT (Real.exp (-6 * p.Bstar)) hd
    (fun j hj => hdenom j.succ (by omega)) (p.c₀ * q / 2) hu hub t ht (hdenom t ht)
  have hexp : -(p.c₀ * (q : ℝ) / 2) ^ 2 /
      (8 * ((3 * q : ℕ) : ℝ) * ((1 + p.Bstar) / Real.exp (-6 * p.Bstar)) ^ 2) =
      -p.occupancyDecay * q := by
    unfold Parameters.occupancyDecay
    push_cast
    field_simp
    ring
  rw [hexp] at hb
  refine le_trans ?_ hb
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, hω.2.trans ?_⟩
  unfold Parameters.rho
  nlinarith [mul_le_mul_of_nonneg_left hcard hd.le]

theorem source_plane_line_card (q : ℕ) (A : FiniteAffine.Plane q P D L) :
    Fintype.card L = q * (q + 1) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset L)) (t := (Finset.univ : Finset D))
    (f := A.direction) (by simp : Set.MapsTo A.direction
      (↑(Finset.univ : Finset L)) (↑(Finset.univ : Finset D)))
  simpa [A.card_lines_direction, A.card_directions, Nat.mul_comm] using h

theorem surviving_all_line_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l)
    (hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ)) (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧ ∃ l,
      ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let E : L → Set (Path (Snapshot I V)) := fun l => {ω | (ω t).1 ≠ none ∧
    ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
      2 * p.rho * q}
  have heq : {ω | (ω t).1 ≠ none ∧ ∃ l,
      ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} = ⋃ l, E l := by
    ext ω
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hs, l, hl⟩
      exact ⟨l, hs, hl⟩
    · rintro ⟨l, hs, hl⟩
      exact ⟨hs, l, hl⟩
  rw [heq]
  refine (measureReal_iUnion_fintype_le E).trans ?_
  calc
    ∑ l, (snapshotPathLaw p q G).real (E l) ≤
        ∑ _l : L, 2 * Real.exp (-p.occupancyDecay * q) := by
      exact Finset.sum_le_sum (fun l _ => surviving_source_occupancy_bound
        p hp q hq hPq hBq G A index line hline l (T l) (hT l) (hcard l) t ht)
    _ = 2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        source_plane_line_card q A, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

theorem source_occupancy_error_tendsto (p : Parameters) (hp : p.Admissible) :
    Tendsto (fun q : ℕ => 2 * (q : ℝ) * (q + 1) *
      Real.exp (-p.occupancyDecay * q)) atTop (nhds 0) := by
  have hκ := p.occupancyDecay_pos hp
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    p.occupancyDecay hκ).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2
    p.occupancyDecay hκ).comp tendsto_natCast_atTop_atTop
  have hsum := (h₂.add h₁).const_mul 2
  convert hsum using 1
  · ext q
    simp only [Function.comp_apply, Real.rpow_one, Real.rpow_two]
    ring
  · norm_num

end Balanced.Selection.Process

end

end OAI
