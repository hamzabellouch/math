import OAI.Geometry.DoublingHilbert.Rectangles

namespace OAI

/-! Fine period grids, energy sampling, and sheet separation. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The measurable periodic selector; boundary values play no role. -/
def stripColor (N : ℕ) (hN : 0 < N) (h t : ℝ) : Fin N :=
  ⟨Int.toNat (⌊t / h⌋ % (N : ℤ)), by
    have hnonneg := Int.emod_nonneg ⌊t / h⌋ (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos ⌊t / h⌋ (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩

theorem measurable_stripColor (N : ℕ) (hN : 0 < N) (h : ℝ) :
    Measurable (stripColor N hN h) := by
  let c : ℤ → Fin N := fun z => ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩
  exact (measurable_of_countable c).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))

theorem inColoredStrip_stripColor (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (ht : ∀ q : ℤ, t ≠ (q : ℝ) * h) :
    inColoredStrip h N (stripColor N hN h t) t := by
  refine ⟨⌊t / h⌋, ?_, ?_, ?_⟩
  · simp only [stripColor]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  · have hle := (le_div_iff₀ hh).mp (Int.floor_le (t / h))
    exact lt_of_le_of_ne hle (ht _).symm
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (t / h))

theorem ae_inColoredStrip_stripColor (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h) :
    ∀ᵐ t, inColoredStrip h N (stripColor N hN h t) t := by
  filter_upwards [ae_all_iff.mpr (fun q : ℤ => volume.ae_ne ((q : ℝ) * h))] with t ht
  exact inColoredStrip_stripColor N hN hh ht

theorem floor_div_of_mem_strip {h t : ℝ} (hh : 0 < h) (q : ℤ)
    (ht : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h)) : ⌊t / h⌋ = q := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ hh).mpr ht.1.le, (div_lt_iff₀ hh).mpr ht.2⟩

theorem stripColor_eq_of_mem_strip (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (q : ℤ) (i : Fin N) (hq : q % (N : ℤ) = (i : ℕ))
    (ht : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h)) :
    stripColor N hN h t = i := by
  apply Fin.ext
  simp only [stripColor, floor_div_of_mem_strip hh q ht, hq, Int.toNat_natCast]

/-- Each color appears exactly once in a complete period block. -/
theorem color_in_block (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (b : ℤ) (i : Fin N)
    (ht : t ∈ Ioo (((b : ℝ) * N + i) * h) (((b : ℝ) * N + i + 1) * h)) :
    stripColor N hN h t = i ∧ inColoredStrip h N i t := by
  let q : ℤ := b * (N : ℤ) + (i : ℕ)
  have hq : q % (N : ℤ) = (i : ℕ) := by
    dsimp [q]
    rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le (i : ℕ)) (by exact_mod_cast i.isLt)
  have hqcast : (q : ℝ) = (b : ℝ) * N + i := by simp [q]
  have ht' : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h) := by rwa [hqcast]
  exact ⟨stripColor_eq_of_mem_strip N hN hh q i hq ht', q, hq, ht'.1, ht'.2⟩

theorem scale_tendsto_zero : Tendsto scale atTop (𝓝 0) := by
  unfold scale
  exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1000 : ℝ)⁻¹| < 1)).comp
    (tendsto_add_atTop_nat 1)

/-- Recurrence supplies arbitrarily fine unused levels with any prescribed pair. -/
theorem exists_fine_level (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (w : Tuple)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j, colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧ scale j < ε := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (scale_tendsto_zero.eventually (gt_mem_nhds hε))
  obtain ⟨j, hj, hc, hw⟩ := recurrent_parameters N W (max J (w.support.sup id + 1)) hN hW
  have hnot : j ∉ w.support := by
    intro hmem
    have hmem' : j ≤ w.support.sup id := Finset.le_sup (f := id) hmem
    omega
  exact ⟨j, hc, hw, Finsupp.notMem_support_iff.mp hnot, hJ j (le_trans (le_max_left _ _) hj)⟩

namespace Segment

/-- Trim an interval to full grid periods, losing at most two periods. -/
theorem exists_grid_inside (I : Segment) {h : ℝ} (hh : 0 < h)
    (hsmall : h < I.length / 4) :
    ∃ (a : ℤ) (n : ℕ) (hn : 0 < n),
      I.lo ≤ (grid (a * h) h n hh hn).lo ∧
      (grid (a * h) h n hh hn).hi ≤ I.hi ∧
      I.length / 2 ≤ (grid (a * h) h n hh hn).length := by
  let a : ℤ := ⌈I.lo / h⌉
  let b : ℤ := ⌊I.hi / h⌋
  have ha₁ : I.lo ≤ (a : ℝ) * h := (div_le_iff₀ hh).mp (Int.le_ceil _)
  have ha₂ : (a : ℝ) * h < I.lo + h := by
    have := (mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (I.lo / h)) hh)
    dsimp [a]
    nlinarith [div_mul_cancel₀ I.lo hh.ne']
  have hb₁ : (b : ℝ) * h ≤ I.hi := (le_div_iff₀ hh).mp (Int.floor_le _)
  have hb₂ : I.hi - h < (b : ℝ) * h := by
    have := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (I.hi / h)) hh
    dsimp [b]
    nlinarith [div_mul_cancel₀ I.hi hh.ne']
  have habr : (a : ℝ) < b := by
    have hlen := I.length_pos
    dsimp [length] at hsmall hlen
    nlinarith
  have hab : a < b := by exact_mod_cast habr
  let n := (b - a).toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hncast : (n : ℝ) = (b : ℝ) - a := by
    have : (n : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  refine ⟨a, n, hn, ha₁, ?_, ?_⟩
  · change (a : ℝ) * h + n * h ≤ I.hi
    rw [hncast]
    nlinarith
  · rw [grid_length, hncast]
    dsimp [length] at hsmall ⊢
    nlinarith

/-- Each component cell lies in its whole grid interval. -/
theorem cell_subset_grid (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (i : Fin n) :
    Icc (cell a h hh i).lo (cell a h hh i).hi ⊆
      Icc (grid a h n hh hn).lo (grid a h n hh hn).hi := by
  intro t ht
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hzero : (0 : ℝ) ≤ i := by positivity
  simp only [cell, grid, Nat.cast_add, Nat.cast_one] at ht ⊢
  rcases ht with ⟨htl, htr⟩
  constructor <;> nlinarith

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

/-- First-moment sampling avoiding every specified null exceptional set. -/
theorem exists_good_le_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ g x ≤ ∫ y, g y ∂μ := by
  obtain ⟨x, hx, hbound⟩ := exists_notMem_null_le_integral hg (ae_iff.mp hP)
  exact ⟨x, by simpa using hx, hbound⟩

theorem exists_le_finite_mean {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    ∃ i, v i ≤ (n : ℝ)⁻¹ * ∑ j, v j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_contra! h
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun i _ => h i)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul] at hs
  exact lt_irrefl _ hs

namespace Segment

@[ext] theorem ext {I J : Segment} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I; cases J; simp_all

theorem grid_subdivision (a h : ℝ) (n N : ℕ) (hh : 0 < h) (hn : 0 < n) (hN : 0 < N) :
    grid a (N * h) n (mul_pos (by exact_mod_cast hN) hh) hn =
      grid a h (n * N) hh (Nat.mul_pos hn hN) := by
  apply ext
  · rfl
  simp only [grid, Nat.cast_mul]
  ring

theorem cell_period_eq_grid (a h : ℝ) (N i : ℕ) (hh : 0 < h) (hN : 0 < N) :
    cell a (N * h) (mul_pos (by exact_mod_cast hN) hh) i =
      grid (a + i * (N * h)) h N hh hN := by
  apply ext
  · rfl
  simp only [cell, grid, Nat.cast_add, Nat.cast_one]
  ring

end Segment

namespace Rectangle

theorem exists_column_integral_le (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) :
    ∃ i : Fin n, (∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh i) J).law) ≤
      (∫ p, g p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) := by
  rw [integral_grid_x a h hh hn J hg, smul_eq_mul]
  exact exists_le_finite_mean hn _

theorem exists_row_integral_le (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (I : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) :
    ∃ i : Fin n, (∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law) ≤
      (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) := by
  rw [integral_grid_y a h hh hn I hg, smul_eq_mul]
  exact exists_le_finite_mean hn _

theorem integral_column_le_mul_grid (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (i : Fin n) :
    (∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh i) J).law) ≤
      n * (∫ p, g p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) := by
  rw [integral_grid_x a h hh hn J hg, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul]
  exact Finset.single_le_sum (f := fun j : Fin n => ∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh j) J).law)
    (fun j _ => integral_nonneg hpos) (Finset.mem_univ i)

theorem integral_row_le_mul_grid (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (I : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (i : Fin n) :
    (∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law) ≤
      n * (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) := by
  rw [integral_grid_y a h hh hn I hg, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul]
  exact Finset.single_le_sum (f := fun j : Fin n => ∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh j)).law)
    (fun j _ => integral_nonneg hpos) (Finset.mem_univ i)

end Rectangle

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

/-- An FTC identity on all subintervals controls all points of a line, not just a.e. points. -/
theorem oscillation_sq_le_segment_energy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (I : Segment) {f g : ℝ → E}
    (hg : IsBoundedField g)
    (hFTC : ∀ a b, (∫ x in a..b, g x) = f b - f a)
    {a b : ℝ} (ha : a ∈ Icc I.lo I.hi) (hb : b ∈ Icc I.lo I.hi) :
    ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) := by
  suffices h : ∀ a b, a ∈ Icc I.lo I.hi → b ∈ Icc I.lo I.hi → a ≤ b →
      ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) by
    rcases le_total a b with hab | hba
    · exact h a b ha hb hab
    · simpa only [norm_sub_rev] using h b a hb ha hba
  intro a b ha hb hab
  have hgi := I.integrable_iff.mp (hg.integrable I.law)
  have hg2i := I.integrable_iff.mp (hg.norm_sq.integrable I.law)
  have hsub : uIcc a b ⊆ uIcc I.lo I.hi := by
    rw [uIcc_of_le hab, uIcc_of_le I.lt.le]
    exact Icc_subset_Icc ha.1 hb.2
  have hgab := hgi.mono_set hsub
  have hg2ab := hg2i.mono_set hsub
  have hcs := norm_integral_sq_le_mass_mul hgab.1 hg2ab.1
  have hcs' : ‖f b - f a‖ ^ 2 ≤ (b - a) * (∫ x in a..b, ‖g x‖ ^ 2) := by
    rw [← hFTC a b, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
    simpa only [measureReal_restrict_apply_univ, Real.volume_real_Ioc,
      max_eq_left (sub_nonneg.mpr hab)] using hcs
  have hmono : (∫ x in a..b, ‖g x‖ ^ 2) ≤
      (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le I.lt.le]
    exact setIntegral_mono_set hg2i.1 (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hx => ⟨ha.1.trans_lt hx.1, hx.2.trans hb.2⟩)
  have hnonneg : 0 ≤ (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) :=
    intervalIntegral.integral_nonneg I.lt.le (fun _ _ => sq_nonneg _)
  have hlen : b - a ≤ I.length := by dsimp [Segment.length]; linarith [ha.1, hb.2]
  calc
    _ ≤ (b - a) * (∫ x in a..b, ‖g x‖ ^ 2) := hcs'
    _ ≤ I.length * (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) :=
      (mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab)).trans
        (mul_le_mul_of_nonneg_right hlen hnonneg)
    _ = _ := by
      rw [I.integral_eq, smul_eq_mul]
      field_simp

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section SheetGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The new sheet's displacement from the base sheet is at most D r wherever it is permitted. -/
theorem globalSheet_offset {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0) {i : ℕ}
    (hi : i < colors j) {p : Base} (hp : p ∈ sheetDomain w) (hip : allowed j i p) :
    ‖globalSheet hf (w.update j (i + 1)) p - globalSheet hf w p‖ ≤ D * scale j := by
  have hup := (admissible_update_iff p w j i hj).mpr ⟨hp, hi, hip⟩
  rw [globalSheet_eqOn hf _ hup, globalSheet_eqOn hf _ hp,
    embeddingSheet_eq f _ p hup, embeddingSheet_eq f _ p hp, ← dist_eq_norm]
  have hs : dist (⟨point p (w.update j (i + 1)), point_mem _ _ hup⟩ : constructedSet)
      ⟨point p w, point_mem _ _ hp⟩ = scale j := by
    change dist (point p (w.update j (i + 1))) (point p w) = scale j
    rw [point_update p w j i hj, dist_eq_norm, add_sub_cancel_left, norm_levelVector]
  exact (hf.dist_le_mul _ _).trans_eq (by rw [hs])

/-- At a crossing two different permitted labels retain their exact Hilbert separation. -/
theorem globalSheet_separation_sq {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ x y, dist x y ≤ dist (f x) (f y))
    (w : Tuple) (j : ℕ) (hj : w j = 0) {i m : ℕ} (him : i ≠ m)
    (hi : i < colors j) (hm : m < colors j) {p : Base} (hp : p ∈ sheetDomain w)
    (hip : allowed j i p) (hmp : allowed j m p) :
    2 * scale j ^ 2 ≤ ‖globalSheet hf (w.update j (i + 1)) p -
      globalSheet hf (w.update j (m + 1)) p‖ ^ 2 := by
  have hup := (admissible_update_iff p w j i hj).mpr ⟨hp, hi, hip⟩
  have hmp' := (admissible_update_iff p w j m hj).mpr ⟨hp, hm, hmp⟩
  rw [globalSheet_eqOn hf _ hup, globalSheet_eqOn hf _ hmp',
    embeddingSheet_eq f _ p hup, embeddingSheet_eq f _ p hmp', ← dist_eq_norm]
  have hs : dist (⟨point p (w.update j (i + 1)), point_mem _ _ hup⟩ : constructedSet)
      ⟨point p (w.update j (m + 1)), point_mem _ _ hmp'⟩ ^ 2 = 2 * scale j ^ 2 := by
    change dist (point p (w.update j (i + 1))) (point p (w.update j (m + 1))) ^ 2 = _
    rw [point_update p w j i hj, point_update p w j m hj, dist_eq_norm,
      add_sub_add_left_eq_sub, norm_levelVector_sub_sq j i m him]
  rw [← hs]
  exact pow_le_pow_left₀ dist_nonneg (hlower _ _) 2

end SheetGeometry

/-- Endpoint bounds on an open real interval extend to its endpoints by continuity. -/
theorem norm_le_on_Icc_of_Ioo {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : Continuous g) {a b R : ℝ} (hab : a < b)
    (hbound : ∀ x ∈ Ioo a b, ‖g x‖ ≤ R) : ∀ x ∈ Icc a b, ‖g x‖ ≤ R := by
  have hsub : Ioo a b ⊆ {x | ‖g x‖ ≤ R} := hbound
  have hcl := closure_minimal hsub (isClosed_le hg.norm continuous_const)
  rw [closure_Ioo hab.ne] at hcl
  exact hcl

end
end DoublingHilbert

end OAI
