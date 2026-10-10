import OAI.Dynamics.TriangleBilliards.Model

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

/-! Elementary facts about complete specular trajectories. -/

lemma reflect_add (e v w : ℂ) : reflect e (v + w) = reflect e v + reflect e w := by
  simp [reflect, mul_add]

lemma reflect_real_smul (e v : ℂ) (r : ℝ) :
    reflect e (r • v) = r • reflect e v := by
  simp only [reflect, star_smul, star_trivial, mul_smul_comm]

lemma reflect_involutive {e : ℂ} (he : e ≠ 0) (v : ℂ) :
    reflect e (reflect e v) = v := by
  simp only [reflect, star_mul', star_div₀, star_star]
  field_simp [he, star_ne_zero.mpr he]

lemma reflect_norm {e : ℂ} (he : e ≠ 0) (v : ℂ) : ‖reflect e v‖ = ‖v‖ := by
  simp [reflect, norm_ne_zero_iff.mpr he]

lemma reflect_tangent {e : ℂ} (he : e ≠ 0) : reflect e e = e := by
  exact div_mul_cancel₀ e (star_ne_zero.mpr he)

lemma reflect_normal {e : ℂ} (he : e ≠ 0) :
    reflect e (Complex.I * e) = -(Complex.I * e) := by
  have h : star e ≠ 0 := star_ne_zero.mpr he
  simp only [reflect, star_mul', Complex.star_def, Complex.conj_I]
  have hc : (starRingEnd ℂ) e ≠ 0 := by simpa only [Complex.star_def] using h
  field_simp [hc]

namespace FlightChain

lemma exists_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    ∃ n : ℤ, c.time n ≤ t ∧ t < c.time (n + 1) := by
  let S : Set ℤ := {n | c.time n ≤ t}
  have hne : S.Nonempty := by
    obtain ⟨n, hn⟩ := c.unbounded_below t
    exact ⟨n, hn.le⟩
  have hbd : BddAbove S := by
    obtain ⟨m, hm⟩ := c.unbounded_above t
    refine ⟨m, ?_⟩
    intro n hn
    exact (c.increasing.lt_iff_lt.mp (lt_of_le_of_lt hn hm)).le
  refine ⟨sSup S, Int.csSup_mem hne hbd, ?_⟩
  by_contra h
  have hsucc : sSup S + 1 ∈ S := le_of_not_gt h
  have hh := le_csSup hbd hsucc
  omega

lemma flight_index_unique {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n m : ℤ} (hn : c.time n ≤ t ∧ t < c.time (n + 1))
    (hm : c.time m ≤ t ∧ t < c.time (m + 1)) : n = m := by
  apply le_antisymm
  · by_contra h
    have hmn : m + 1 ≤ n := by omega
    have := c.increasing.monotone hmn
    linarith [hn.1, hm.2]
  · by_contra h
    have hnm : n + 1 ≤ m := by omega
    have := c.increasing.monotone hnm
    linarith [hm.1, hn.2]

lemma at_of_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (hn : c.time n ≤ t ∧ t < c.time (n + 1)) :
    c.at t = (c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n) := by
  classical
  have hex := c.exists_flight t
  have hi := c.flight_index_unique (Classical.choose_spec hex) hn
  simp only [FlightChain.at, dite_eq_left hex, hi]

lemma at_zero {Q : Triangle} {z : Phase} (c : FlightChain Q z) : c.at 0 = z := by
  have h : c.time 0 ≤ 0 ∧ 0 < c.time (0 + 1) := by
    simpa using And.intro c.zero_before.le c.zero_after
  rw [c.at_of_flight h]
  apply Prod.ext
  · simpa using c.start_point.symm
  · exact c.start_direction.symm

lemma initial_inside {Q : Triangle} {z : Phase} (c : FlightChain Q z) : z.1 ∈ Q.table := by
  have h := c.inside 0 0 c.zero_before (by simpa using c.zero_after)
  rw [c.start_point]
  simpa only [zero_sub] using h

lemma position_at_interior {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (h₁ : c.time n < t) (h₂ : t < c.time (n + 1)) :
    (c.at t).1 ∈ Q.table := by
  rw [c.at_of_flight ⟨h₁.le, h₂⟩]
  exact c.inside n t h₁ h₂

lemma constant_direction_on_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (h : c.time n ≤ t ∧ t < c.time (n + 1)) :
    (c.at t).2 = c.direction n := by
  rw [c.at_of_flight h]

lemma unit_speed_on_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {s t : ℝ} {n : ℤ} (hs : c.time n ≤ s ∧ s < c.time (n + 1))
    (ht : c.time n ≤ t ∧ t < c.time (n + 1)) :
    dist (c.at s).1 (c.at t).1 = |s - t| := by
  rw [c.at_of_flight hs, c.at_of_flight ht]
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul, Circle.norm_coe]
  simp [Real.norm_eq_abs]

end FlightChain

lemma billiardFlow_zero (Q : Triangle) (z : Phase) : billiardFlow Q 0 z = z := by
  classical
  by_cases h : Nonempty (FlightChain Q z)
  · simp only [billiardFlow, dite_eq_left h, FlightChain.at_zero]
  · simp only [billiardFlow, dite_eq_right h]

namespace Triangle

lemma isOpen_table (Q : Triangle) : IsOpen Q.table := isOpen_interior

lemma measurableSet_table (Q : Triangle) : MeasurableSet Q.table :=
  Q.isOpen_table.measurableSet

lemma table_nonempty (Q : Triangle) : Q.table.Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  apply Q.nondegenerate.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Complex.finrank_real_complex]

lemma area_pos (Q : Triangle) : 0 < volume Q.table :=
  Q.isOpen_table.measure_pos volume Q.table_nonempty

lemma area_lt_top (Q : Triangle) : volume Q.table < ⊤ := by
  apply lt_of_le_of_lt (measure_mono interior_subset)
  exact ((finite_range Q.vertex).isCompact_convexHull ℝ).measure_lt_top

lemma normalized_area_univ (Q : Triangle) :
    ((volume Q.table)⁻¹ • volume.restrict Q.table) univ = 1 := by
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel Q.area_pos.ne' Q.area_lt_top.ne

lemma tangent_ne_zero (Q : Triangle) (i : Fin 3) : Q.tangent i ≠ 0 := by
  simp only [tangent, sub_ne_zero]
  exact Q.nondegenerate.injective.ne (by decide +revert)

end Triangle

lemma angularMeasure_univ : angularMeasure univ = 1 := by
  rw [angularMeasure, Measure.map_apply Circle.exp.continuous.measurable MeasurableSet.univ]
  simp only [preimage_univ, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ico, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

instance angularMeasure_probability : IsProbabilityMeasure angularMeasure :=
  ⟨angularMeasure_univ⟩

lemma phaseMeasure_univ (Q : Triangle) : phaseMeasure Q univ = 1 := by
  rw [phaseMeasure, ← univ_prod_univ, Measure.prod_prod,
    Q.normalized_area_univ, angularMeasure_univ, mul_one]

instance phaseMeasure_probability (Q : Triangle) : IsProbabilityMeasure (phaseMeasure Q) :=
  ⟨phaseMeasure_univ Q⟩

namespace Triangle

/-- Barycentric coordinates for the exact, nondegenerate table. -/
def basis (Q : Triangle) : AffineBasis (Fin 3) ℝ ℂ where
  toFun := Q.vertex
  ind' := Q.nondegenerate
  tot' := Q.nondegenerate.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by simp [Complex.finrank_real_complex])

lemma table_iff_coords (Q : Triangle) (x : ℂ) :
    x ∈ Q.table ↔ ∀ i, 0 < Q.basis.coord i x := by
  change x ∈ interior (convexHull ℝ (range Q.basis)) ↔ _
  rw [Q.basis.interior_convexHull]
  rfl

lemma side_coord_zero_iff (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) (k : Fin 3) : Q.basis.coord k x = 0 ↔ k = i + 2 := by
  rw [side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  change Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) t) = 0 ↔ _
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  fin_cases i <;> fin_cases k <;>
    norm_num [ne_of_gt ht.1, ne_of_gt (sub_pos.mpr ht.2)]

lemma side_not_table (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) : x ∉ Q.table := by
  intro h
  have hp := (Q.table_iff_coords x).mp h (i + 2)
  have hz := (Q.side_coord_zero_iff hx (i + 2)).mpr rfl
  linarith

lemma side_index_unique (Q : Triangle) {x : ℂ} {i j : Fin 3}
    (hi : x ∈ Q.side i) (hj : x ∈ Q.side j) : i = j := by
  apply add_right_cancel (b := (2 : Fin 3))
  exact (Q.side_coord_zero_iff hj (i + 2)).mp
    ((Q.side_coord_zero_iff hi (i + 2)).mpr rfl)

end Triangle

/-- The irrational-holonomy scalar for every irrational angle,
with no Diophantine bound. -/
lemma irrational_holonomy_ne_one {α : ℝ} (hα : Irrational (α / Real.pi))
    {j : ℤ} (hj : j ≠ 0) :
    Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hn
  norm_num [Complex.mul_re, Complex.mul_im] at him
  apply (irrational_iff_ne_rational _).mp hα n j hj
  apply (div_eq_div_iff Real.pi_ne_zero (Int.cast_ne_zero.mpr hj)).mpr
  nlinarith [him]

lemma parallel_mode_zero {α : ℝ} (hα : Irrational (α / Real.pi))
    {j : ℤ} (hj : j ≠ 0) {c : ℂ}
    (hc : Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) * c = c) : c = 0 := by
  have hz : (Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) - 1) * c = 0 := by
    rw [sub_mul, hc, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (irrational_holonomy_ne_one hα hj))

/-- The reflection is a genuine real-linear Euclidean isometry. -/
def reflectIsometry (e : ℂ) (he : e ≠ 0) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun := reflect e
  invFun := reflect e
  left_inv := reflect_involutive he
  right_inv := reflect_involutive he
  map_add' := reflect_add e
  map_smul' := fun r v => reflect_real_smul e v r
  norm_map' := reflect_norm he

lemma exit_time_unique (P : ℝ → Prop) {a b c : ℝ}
    (hab : a < b) (hac : a < c)
    (h₁ : ∀ t, a < t → t < b → P t) (h₂ : ∀ t, a < t → t < c → P t)
    (hb : ¬ P b) (hc : ¬ P c) : b = c := by
  rcases lt_trichotomy b c with h | h | h
  · exact (hb (h₂ b hab h)).elim
  · exact h
  · exact (hc (h₁ c hac h)).elim

lemma entry_time_unique (P : ℝ → Prop) {a b c : ℝ}
    (hac : a < c) (hbc : b < c)
    (h₁ : ∀ t, a < t → t < c → P t) (h₂ : ∀ t, b < t → t < c → P t)
    (ha : ¬ P a) (hb : ¬ P b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (hb (h₁ b h hbc)).elim
  · exact h
  · exact (ha (h₂ a h hac)).elim

end TriangularBilliards
end

end OAI
