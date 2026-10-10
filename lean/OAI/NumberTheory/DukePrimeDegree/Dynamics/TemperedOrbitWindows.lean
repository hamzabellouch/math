import OAI.NumberTheory.DukePrimeDegree.Geometry.TemperedChartRadius

namespace OAI

/-! # Uniform subexponential chart control on finite orbit windows

The maximal height on the first N iterates is still sublinear. This
retains the local chart radius simultaneously along the whole word,
without an integrability assumption on the cusp height.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

def windowHeight {Y : Type*} (T : Y → Y) (H : Y → ℕ) (N : ℕ) (x : Y) : ℕ :=
  (Finset.range (N+1)).sup (fun k => H (T^[k] x))

lemma height_le_windowHeight {Y : Type*} (T : Y → Y) (H : Y → ℕ)
    {k N : ℕ} (hk : k ≤ N) (x : Y) : H (T^[k] x) ≤ windowHeight T H N x := by
  exact Finset.le_sup (f := fun k => H (T^[k] x)) (Finset.mem_range.mpr (by omega))

theorem ae_windowHeight_affine_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ, ∃ C : ℕ, ∀ N : ℕ, (windowHeight T H N x : ℝ) ≤ C+δ*N := by
  filter_upwards [ae_height_affine_bound μ hT H hH hstep hδ] with x hx
  obtain ⟨C,hC⟩ := hx
  refine ⟨C,fun N => ?_⟩
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup (Finset.range (N+1))
    (Finset.nonempty_range_iff.mpr (by omega)) (fun k => H (T^[k] x))
  change (((Finset.range (N+1)).sup (fun k => H (T^[k] x)) : ℕ) : ℝ) ≤ _
  rw [he]
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hmul := mul_le_mul_of_nonneg_left hkN hδ.le
  linarith [hC k]

theorem ae_windowHeight_div_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1) :
    ∀ᵐ x ∂μ, Tendsto (fun N : ℕ => (windowHeight T H N x : ℝ)/(N:ℝ))
      atTop (𝓝 0) := by
  have hbound (q : ℕ) := ae_windowHeight_affine_bound μ hT H hH hstep
    (show 0 < 1/(q+1:ℝ) by positivity)
  filter_upwards [ae_all_iff.mpr hbound] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨C,hC⟩ := hx q
  have hlim : Tendsto (fun N : ℕ => (C:ℝ)/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)),eventually_ge_atTop 1]
    with N hN hNone
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hNone
  have hf := div_le_div_of_nonneg_right (hC N) hNp.le
  rw [add_div,mul_div_cancel_right₀ _ hNp.ne'] at hf
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNp.le)]
  linarith

/-- One radius works at every time in an N-letter orbit window. -/
theorem ae_window_local_injectivity_subexponential (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ k ≤ N,
      LocalInjectivityAt (Real.exp (-ε*(N:ℝ)))
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  obtain ⟨κ,H,hκ,hH,hinj,hstep⟩ := exists_local_injectivity_height ell hell
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  filter_upwards [ae_windowHeight_div_tendsto_zero μ hT H hH (fun x => (hstep x).1)]
    with x hx
  intro ε hε
  filter_upwards [radius_eventually_ge_exp_of_sublinear hκ hx hε] with N hN
  intro k hk
  exact (hinj _).mono (hN.trans (pow_le_pow_of_le_one
    (inv_nonneg.mpr (zero_lt_one.trans hκ).le) (inv_le_one_of_one_le₀ hκ.le)
    (height_le_windowHeight T H hk x)))

end DukePrimeDegree

end

end OAI
