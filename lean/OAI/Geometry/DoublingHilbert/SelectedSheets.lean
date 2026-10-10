import OAI.Geometry.DoublingHilbert.Grids

namespace OAI

/-! Periodic selections of sheets and stripewise derivative means. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace IsBoundedField
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem add {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.add hg.1, M + N,
    fun x => (norm_add_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem const_mul {g : X → ℝ} (hg : IsBoundedField g) (r : ℝ) :
    IsBoundedField (fun x => r * g x) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.const_mul r, ‖r‖ * M, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg r)

end IsBoundedField

section StripeMeans
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Horizontal integration on each separate vertical strip; discontinuous selections
are never differentiated across strip boundaries. -/
theorem horizontal_mean_bound_stripes {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {F : Base → E} {G : ι → Base → E}
    {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) (c : Fin n → ι) {R : ℝ}
    (hcolor : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, σ x = c i)
    (hbound : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, ∀ y ∈ Ioo J.lo J.hi, ‖G (c i) (x, y) - F (x, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) -
      (∫ p, column F (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law)‖ ≤
      2 * R / h := by
  let Q : Rectangle := ⟨Segment.grid a h n hh hn, J⟩
  let Qi (i : Fin n) : Rectangle := ⟨Segment.cell a h hh i, J⟩
  have hB : IsBoundedField (fun p => column (G (σ p.1)) (1, 0) p) :=
    IsBoundedField.select (fun i => boundedField_column (hG i) (1, 0))
      (hσ.comp measurable_fst)
  have hBF := boundedField_column hF (1, 0)
  have hcell : ∀ i : Fin n,
      ‖∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law‖ ≤ 2 * R / h := by
    intro i
    have hend : ∀ y ∈ Ioo J.lo J.hi, ∀ x ∈ Icc (Qi i).x.lo (Qi i).x.hi,
        ‖G (c i) (x, y) - F (x, y)‖ ≤ R := by
      intro y hy
      apply norm_le_on_Icc_of_Ioo
        (((hG (c i)).continuous.comp (continuous_id.prodMk continuous_const)).sub
          (hF.continuous.comp (continuous_id.prodMk continuous_const))) (Qi i).x.lt
      exact fun x hx => hbound i x hx y hy
    have he := horizontal_mean_bound (Qi i) hF hG (σ := fun _ => c i) measurable_const
      (J.ae_mem.mono fun y hy => hend y hy _ ⟨le_rfl, (Qi i).x.lt.le⟩)
      (J.ae_mem.mono fun y hy => hend y hy _ ⟨(Qi i).x.lt.le, le_rfl⟩)
    have hBC := boundedField_column (hG (c i)) (1, 0)
    rw [← integral_sub (hBC.integrable _) (hBF.integrable _)] at he
    have heq : (∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law) =
        ∫ p, column (G (c i)) (1, 0) p - column F (1, 0) p ∂(Qi i).law := by
      apply integral_congr_ae
      filter_upwards [(Qi i).ae_mem] with p hp
      rw [hcolor i p.1 hp.1]
    rw [heq]
    simpa only [Qi, Segment.cell_length] using he
  rw [← integral_sub (hB.integrable _) (hBF.integrable _),
    Rectangle.integral_grid_x a h hh hn J (hB.sub hBF)]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
        ‖∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (2 * R / h) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => hcell i
    _ = 2 * R / h := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul]

end StripeMeans
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

def stripWidth (j : ℕ) : ℝ := (widthFactor j : ℝ) * scale j

theorem stripWidth_pos (j : ℕ) : 0 < stripWidth j :=
  mul_pos (by exact_mod_cast widthFactor_pos j) (scale_pos j)

def xPeriod (j : ℕ) : ℝ := (colors j : ℝ) * stripWidth j

def yPeriod (j : ℕ) : ℝ := (colors j : ℝ) * scale j

theorem xPeriod_pos (j : ℕ) : 0 < xPeriod j :=
  mul_pos (by exact_mod_cast colors_pos j) (stripWidth_pos j)

theorem yPeriod_pos (j : ℕ) : 0 < yPeriod j :=
  mul_pos (by exact_mod_cast colors_pos j) (scale_pos j)

/-- A finite rectangle of complete level-j period blocks. -/
structure PeriodGrid (j : ℕ) where
  ax : ℤ
  ay : ℤ
  nx : ℕ
  ny : ℕ
  nx_pos : 0 < nx
  ny_pos : 0 < ny

namespace PeriodGrid
variable {j : ℕ}

def rectangle (G : PeriodGrid j) : Rectangle :=
  ⟨Segment.grid (G.ax * xPeriod j) (xPeriod j) G.nx (xPeriod_pos j) G.nx_pos,
   Segment.grid (G.ay * yPeriod j) (yPeriod j) G.ny (yPeriod_pos j) G.ny_pos⟩

theorem exists_inside (Q : Rectangle)
    (hx : xPeriod j < Q.x.length / 4) (hy : yPeriod j < Q.y.length / 4) :
    ∃ G : PeriodGrid j, G.rectangle.closed ⊆ Q.closed ∧
      Q.x.length / 2 ≤ G.rectangle.x.length ∧
      Q.y.length / 2 ≤ G.rectangle.y.length := by
  obtain ⟨ax, nx, hnx, hxl, hxr, hxs⟩ :=
    Q.x.exists_grid_inside (xPeriod_pos j) hx
  obtain ⟨ay, ny, hny, hyl, hyr, hys⟩ :=
    Q.y.exists_grid_inside (yPeriod_pos j) hy
  refine ⟨⟨ax, ay, nx, ny, hnx, hny⟩, ?_, hxs, hys⟩
  rintro p ⟨hp, hq⟩
  exact ⟨⟨hxl.trans hp.1, hp.2.trans hxr⟩, ⟨hyl.trans hq.1, hq.2.trans hyr⟩⟩

def block (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) : Rectangle :=
  ⟨Segment.cell (G.ax * xPeriod j) (xPeriod j) (xPeriod_pos j) a,
   Segment.cell (G.ay * yPeriod j) (yPeriod j) (yPeriod_pos j) b⟩

theorem block_subset (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).closed ⊆ G.rectangle.closed := by
  rintro p ⟨hp, hq⟩
  exact ⟨Segment.cell_subset_grid _ _ (xPeriod_pos j) G.nx_pos a hp,
    Segment.cell_subset_grid _ _ (yPeriod_pos j) G.ny_pos b hq⟩

theorem exists_block_integral_le (G : PeriodGrid j) {g : Base → ℝ}
    (hg : IsBoundedField g) :
    ∃ a : Fin G.nx, ∃ b : Fin G.ny,
      (∫ p, g p ∂(G.block a b).law) ≤ ∫ p, g p ∂G.rectangle.law := by
  obtain ⟨a, ha⟩ := Rectangle.exists_column_integral_le _ _ (xPeriod_pos j) G.nx_pos
    G.rectangle.y hg
  obtain ⟨b, hb⟩ := Rectangle.exists_row_integral_le _ _ (yPeriod_pos j) G.ny_pos
    (Segment.cell (G.ax * xPeriod j) (xPeriod j) (xPeriod_pos j) a) hg
  exact ⟨a, b, hb.trans ha⟩

theorem rectangle_x_subdivided (G : PeriodGrid j) : G.rectangle.x =
    Segment.grid (G.ax * xPeriod j) (stripWidth j) (G.nx * colors j)
      (stripWidth_pos j) (Nat.mul_pos G.nx_pos (colors_pos j)) :=
  Segment.grid_subdivision _ _ _ _ (stripWidth_pos j) G.nx_pos (colors_pos j)

theorem block_x (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).x = Segment.grid (((G.ax : ℝ) + a) * xPeriod j) (stripWidth j)
      (colors j) (stripWidth_pos j) (colors_pos j) := by
  apply Segment.ext
  · simp [block, Segment.cell, Segment.grid]; ring
  · simp [block, Segment.cell, Segment.grid, xPeriod]; ring

theorem block_y (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).y = Segment.grid (((G.ay : ℝ) + b) * yPeriod j) (scale j)
      (colors j) (scale_pos j) (colors_pos j) := by
  apply Segment.ext
  · simp [block, Segment.cell, Segment.grid]; ring
  · simp [block, Segment.cell, Segment.grid, yPeriod]; ring

end PeriodGrid

def residueColor (N : ℕ) (hN : 0 < N) (q : ℤ) : Fin N :=
  ⟨(q % (N : ℤ)).toNat, by
    exact (Int.toNat_lt' hN).mpr
      (Int.emod_lt_of_pos q (by exact_mod_cast hN))⟩

theorem residueColor_val (N : ℕ) (hN : 0 < N) (q : ℤ) :
    ((residueColor N hN q : Fin N) : ℤ) = q % (N : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg q (by exact_mod_cast hN.ne'))

theorem color_on_cell (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (a : ℤ) (i : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (Segment.cell (a * h) h hh i).lo (Segment.cell (a * h) h hh i).hi) :
    stripColor N hN h t = residueColor N hN (a + i) ∧
      inColoredStrip h N (residueColor N hN (a + i)) t := by
  have ht' : t ∈ Ioo (((a + (i : ℤ) : ℤ) : ℝ) * h)
      ((((a + (i : ℤ) : ℤ) : ℝ) + 1) * h) := by
    simp only [Segment.cell, Nat.cast_add, Nat.cast_one] at ht
    push_cast
    constructor <;> nlinarith [ht.1, ht.2]
  have hq := (residueColor_val N hN (a + i)).symm
  exact ⟨stripColor_eq_of_mem_strip N hN hh _ _ hq ht', _, hq, ht'.1, ht'.2⟩

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace Rectangle

theorem interior_subset_closed (Q : Rectangle) : Q.interior ⊆ Q.closed := by
  rintro p ⟨hp, hq⟩
  exact ⟨⟨hp.1.le, hp.2.le⟩, ⟨hq.1.le, hq.2.le⟩⟩

end Rectangle

section SelectedSheets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def addedSheet {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (i : Fin (colors j)) : Base → E :=
  globalSheet hf (w.update j ((i : ℕ) + 1))

def horizontalColumn {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (v : Base) (p : Base) : E :=
  column (addedSheet hf w j (stripColor (colors j) (colors_pos j) (scale j) p.2)) v p

def verticalColumn {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (v : Base) (p : Base) : E :=
  column (addedSheet hf w j (stripColor (colors j) (colors_pos j) (stripWidth j) p.1)) v p

omit [CompleteSpace E] in
theorem bounded_horizontalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (horizontalColumn hf w j v) := by
  unfold horizontalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (scale j)).comp measurable_snd)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

omit [CompleteSpace E] in
theorem bounded_verticalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (verticalColumn hf w j v) := by
  unfold verticalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (stripWidth j)).comp measurable_fst)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

theorem ae_horizontal_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ∀ᵐ p ∂Q.law, (‖horizontalColumn hf w j (1, 0) p‖ ^ 2,
      ‖horizontalColumn hf w j (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  have hg : ∀ᵐ p, ∀ i : Fin (colors j), p ∈ sheetDomain (w.update j ((i : ℕ) + 1)) →
      (‖column (addedSheet hf w j i) (1, 0) p‖ ^ 2,
       ‖column (addedSheet hf w j i) (0, 1) p‖ ^ 2) ∈ derivativeCompact f :=
    ae_all_iff.mpr fun i => ae_globalSheet_pair hf _
  have hs : ∀ᵐ p ∂Q.law,
      inColoredStrip (scale j) (colors j) (stripColor (colors j) (colors_pos j) (scale j) p.2) p.2 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Q.y.ae_of_ae (ae_inColoredStrip_stripColor _ _ (scale_pos j)))
  filter_upwards [Q.ae_of_ae hg, Q.ae_mem, hs] with p hp hmem hstrip
  exact hp _ ((admissible_update_iff p w j _ hj).mpr
    ⟨hQ (Q.interior_subset_closed hmem), (stripColor _ _ _ _).isLt, Or.inl hstrip⟩)

theorem ae_vertical_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ∀ᵐ p ∂Q.law, (‖verticalColumn hf w j (1, 0) p‖ ^ 2,
      ‖verticalColumn hf w j (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  have hg : ∀ᵐ p, ∀ i : Fin (colors j), p ∈ sheetDomain (w.update j ((i : ℕ) + 1)) →
      (‖column (addedSheet hf w j i) (1, 0) p‖ ^ 2,
       ‖column (addedSheet hf w j i) (0, 1) p‖ ^ 2) ∈ derivativeCompact f :=
    ae_all_iff.mpr fun i => ae_globalSheet_pair hf _
  have hs : ∀ᵐ p ∂Q.law,
      inColoredStrip (stripWidth j) (colors j)
        (stripColor (colors j) (colors_pos j) (stripWidth j) p.1) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae
      (Q.x.ae_of_ae (ae_inColoredStrip_stripColor _ _ (stripWidth_pos j)))
  filter_upwards [Q.ae_of_ae hg, Q.ae_mem, hs] with p hp hmem hstrip
  exact hp _ ((admissible_update_iff p w j _ hj).mpr
    ⟨hQ (Q.interior_subset_closed hmem), (stripColor _ _ _ _).isLt, Or.inr hstrip⟩)

theorem horizontalColumn_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ‖(∫ p, horizontalColumn hf w j (1, 0) p ∂Q.law) -
      (∫ p, column (globalSheet hf w) (1, 0) p ∂Q.law)‖ ≤
      2 * D * scale j / Q.x.length := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  choose C' hG using fun i : Fin (colors j) =>
    globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hend : ∀ x ∈ Icc Q.x.lo Q.x.hi, ∀ᵐ y ∂Q.y.law,
      ‖addedSheet hf w j (stripColor (colors j) (colors_pos j) (scale j) y) (x, y) -
        globalSheet hf w (x, y)‖ ≤ D * scale j := by
    intro x hx
    filter_upwards [Q.y.ae_mem,
      Q.y.ae_of_ae (ae_inColoredStrip_stripColor _ _ (scale_pos j))] with y hy hc
    exact globalSheet_offset hf w j hj (stripColor _ _ _ _).isLt
      (hQ ⟨hx, hy.1.le, hy.2.le⟩) (Or.inl hc)
  simpa only [mul_assoc, horizontalColumn, addedSheet] using horizontal_mean_bound Q hF hG
    (measurable_stripColor _ _ _) (hend _ ⟨le_rfl, Q.x.lt.le⟩)
      (hend _ ⟨Q.x.lt.le, le_rfl⟩)

theorem verticalColumn_y_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (0, 1) p ∂Q.law) -
      (∫ p, column (globalSheet hf w) (0, 1) p ∂Q.law)‖ ≤
      2 * D * scale j / Q.y.length := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  choose C' hG using fun i : Fin (colors j) =>
    globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hend : ∀ y ∈ Icc Q.y.lo Q.y.hi, ∀ᵐ x ∂Q.x.law,
      ‖addedSheet hf w j (stripColor (colors j) (colors_pos j) (stripWidth j) x) (x, y) -
        globalSheet hf w (x, y)‖ ≤ D * scale j := by
    intro y hy
    filter_upwards [Q.x.ae_mem,
      Q.x.ae_of_ae (ae_inColoredStrip_stripColor _ _ (stripWidth_pos j))] with x hx hc
    exact globalSheet_offset hf w j hj (stripColor _ _ _ _).isLt
      (hQ ⟨⟨hx.1.le, hx.2.le⟩, hy⟩) (Or.inr hc)
  simpa only [mul_assoc, verticalColumn, addedSheet] using vertical_mean_bound Q hF hG
    (measurable_stripColor _ _ _) (hend _ ⟨le_rfl, Q.y.lt.le⟩)
      (hend _ ⟨Q.y.lt.le, le_rfl⟩)

end SelectedSheets
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section VerticalStripeMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The discontinuous vertical selection is integrated strip by strip. -/
theorem verticalColumn_x_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (1, 0) p ∂G.rectangle.law) -
      (∫ p, column (globalSheet hf w) (1, 0) p ∂G.rectangle.law)‖ ≤
      2 * D / (widthFactor j : ℝ) := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  choose C' hG using fun i : Fin (colors j) =>
    globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  let a : ℤ := G.ax * (colors j : ℤ)
  let n := G.nx * colors j
  have hn : 0 < n := Nat.mul_pos G.nx_pos (colors_pos j)
  have ha : (a : ℝ) * stripWidth j = G.ax * xPeriod j := by
    simp only [a, Int.cast_mul, Int.cast_natCast, xPeriod]; ring
  let c : Fin n → Fin (colors j) := fun i => residueColor (colors j) (colors_pos j) (a + i)
  let J := G.rectangle.y
  let Q' : Rectangle := ⟨Segment.grid (a * stripWidth j) (stripWidth j) n
    (stripWidth_pos j) hn, J⟩
  have hrect : Q' = G.rectangle := by
    have hx := G.rectangle_x_subdivided
    rw [← ha] at hx
    exact congrArg (fun I => Rectangle.mk I G.rectangle.y) hx.symm
  have hc : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).lo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).hi,
      stripColor (colors j) (colors_pos j) (stripWidth j) x = c i := by
    intro i x hx
    exact (color_on_cell _ _ (stripWidth_pos j) a i hx).1
  have hb : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).lo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).hi, ∀ y ∈ Ioo J.lo J.hi,
      ‖addedSheet hf w j (c i) (x, y) - globalSheet hf w (x, y)‖ ≤ D * scale j := by
    intro i x hx y hy
    have hxQ := Segment.cell_subset_grid (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) hn i ⟨hx.1.le, hx.2.le⟩
    have hp : (x, y) ∈ G.rectangle.closed := by
      rw [← hrect]
      exact ⟨hxQ, hy.1.le, hy.2.le⟩
    exact globalSheet_offset hf w j hj (c i).isLt (hQ hp)
      (Or.inr (color_on_cell _ _ (stripWidth_pos j) a i hx).2)
  have hm := horizontal_mean_bound_stripes (a * stripWidth j) (stripWidth j)
    (stripWidth_pos j) hn J hF hG (measurable_stripColor _ _ _) c hc hb
  change ‖(∫ p, verticalColumn hf w j (1, 0) p ∂Q'.law) -
    (∫ p, column (globalSheet hf w) (1, 0) p ∂Q'.law)‖ ≤ _ at hm
  rw [hrect] at hm
  convert hm using 1
  unfold stripWidth
  field_simp [ne_of_gt (scale_pos j)]

end VerticalStripeMean
end
end DoublingHilbert

end OAI
