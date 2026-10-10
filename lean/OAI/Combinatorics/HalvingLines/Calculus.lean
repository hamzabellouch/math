import OAI.Combinatorics.HalvingLines.Zoom

namespace OAI

namespace PlanarHalving

namespace Calculus

open Filter MeasureTheory Set Metric Asymptotics
open scoped Topology ENNReal NNReal

theorem ae_near_set (S : Set Point) (hS : MeasurableSet S) :
    ∀ᵐ x ∂(volume : Measure Point), x ∈ S →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x,
        ∃ z ∈ S, dist z y ≤ ε * dist y x := by
  have hd : ∀ᵐ x ∂(volume : Measure Point).restrict S, ∀ n : ℕ,
      ∀ {ι : Type} {l : Filter ι} (w : ι → Point) (δ : ι → ℝ),
      Tendsto δ l (𝓝[>] 0) →
      (∀ᶠ j in l, x ∈ closedBall (w j) ((n + 1 : ℝ) * δ j)) →
      Tendsto (fun j => volume (S ∩ closedBall (w j) (δ j)) /
        volume (closedBall (w j) (δ j))) l (𝓝 (1 : ℝ≥0∞)) := by
    rw [ae_all_iff]
    intro n
    exact IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume S (n + 1)
  rw [ae_restrict_iff' hS] at hd
  filter_upwards [hd] with x hx hxs
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (ε⁻¹)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hnε : (n + 1 : ℝ)⁻¹ ≤ ε := by
    apply (inv_le_iff_one_le_mul₀ hn0).mpr
    have hh := (inv_lt_iff_one_lt_mul₀ hε).mp hn
    nlinarith
  have hδ : Tendsto (fun y : Point => (n + 1 : ℝ)⁻¹ * dist y x)
      (𝓝[≠] x) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hh : Tendsto (fun y : Point => (n + 1 : ℝ)⁻¹ * dist y x)
          (𝓝 x) (𝓝 ((n + 1 : ℝ)⁻¹ * dist x x)) :=
        (continuousAt_id.dist continuousAt_const).const_mul _
      simpa using hh.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact mul_pos (inv_pos.mpr hn0) (dist_pos.mpr hy)
  have hcover : ∀ᶠ y : Point in 𝓝[≠] x,
      x ∈ closedBall y ((n + 1 : ℝ) * ((n + 1 : ℝ)⁻¹ * dist y x)) := by
    filter_upwards with y
    simp [Metric.mem_closedBall, mul_inv_cancel_left₀ hn0.ne', dist_comm]
  have hlim := hx hxs n (fun y : Point => y)
    (fun y => (n + 1 : ℝ)⁻¹ * dist y x) hδ hcover
  have he : ∀ᶠ y : Point in 𝓝[≠] x,
      ∃ z ∈ S, dist z y ≤ ε * dist y x := by
    have hh := hlim.eventually (Ioi_mem_nhds (show (0 : ℝ≥0∞) < 1 by simp))
    filter_upwards [hh] with y hy
    have hne : volume (S ∩ closedBall y ((n + 1 : ℝ)⁻¹ * dist y x)) ≠ 0 := by
      intro hz
      simp [hz] at hy
    obtain ⟨z, hzS, hzB⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨z, hzS, (Metric.mem_closedBall.mp hzB).trans
      (mul_le_mul_of_nonneg_right hnε dist_nonneg)⟩
  rw [← nhdsNE_sup_pure x, Filter.eventually_sup]
  exact ⟨he, by simp only [Filter.eventually_pure]; exact ⟨x, hxs, by simp⟩⟩

theorem hasFDerivAt_of_within_near_set {f : Point → ℝ} {S : Set Point}
    {x : Point} {f' : Point →L[ℝ] ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ z ∈ S, ∀ y, ‖f y - f z‖ ≤ C * ‖y - z‖)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x,
      ∃ z ∈ S, dist z y ≤ ε * dist y x)
    (hf : HasFDerivWithinAt f f' S x) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply IsLittleO.of_bound
  intro ε hε
  let η := min 1 (ε / (2 * (C + ‖f'‖ + 1)))
  have hden : 0 < 2 * (C + ‖f'‖ + 1) := by positivity
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hsmall : (C + ‖f'‖) * η ≤ ε / 2 := by
    have hh := (le_div_iff₀ hden).mp (min_le_right 1 (ε / (2 * (C + ‖f'‖ + 1))))
    nlinarith only [hh, hη]
  have hlin := hf.isLittleO.def (show 0 < ε / 4 by positivity)
  obtain ⟨r, hr, hrlin⟩ := Metric.mem_nhdsWithin_iff.mp hlin
  filter_upwards [hnear η hη, Metric.ball_mem_nhds x (show 0 < r / 2 by positivity)] with y hy hyr
  obtain ⟨z, hzS, hzy⟩ := hy
  have hyz : ‖y - z‖ ≤ η * ‖y - x‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hzy
  have hzx : ‖z - x‖ ≤ 2 * ‖y - x‖ := by
    have hh := dist_triangle z y x
    simp only [dist_eq_norm] at hh
    have hzy' : ‖z - y‖ ≤ ‖y - x‖ := by
      have hzyη : ‖z - y‖ ≤ η * ‖y - x‖ := by
        rw [norm_sub_rev]
        exact hyz
      exact hzyη.trans (mul_le_of_le_one_left (norm_nonneg _) hη1)
    linarith only [hh, hzy']
  have hzr : dist z x < r := by
    rw [Metric.mem_ball, dist_eq_norm] at hyr
    rw [dist_eq_norm]
    linarith only [hzx, hyr]
  have hzlin := hrlin ⟨hzr, hzS⟩
  have hdecomp : f y - f x - f' (y - x) =
      (f y - f z - f' (y - z)) + (f z - f x - f' (z - x)) := by
    rw [show y - x = (y - z) + (z - x) by abel, map_add]
    ring
  calc
    ‖f y - f x - f' (y - x)‖ ≤
        ‖f y - f z‖ + ‖f' (y - z)‖ + ‖f z - f x - f' (z - x)‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ C * ‖y - z‖ + ‖f'‖ * ‖y - z‖ + (ε / 4) * ‖z - x‖ := by
      gcongr
      · exact hLip z hzS y
      · exact f'.le_opNorm _
      · exact hzlin
    _ ≤ (C + ‖f'‖) * (η * ‖y - x‖) + (ε / 4) * (2 * ‖y - x‖) := by
      rw [← add_mul]
      gcongr
    _ ≤ ε * ‖y - x‖ := by
      nlinarith only [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (y - x))]

theorem ae_differentiable_of_pointwise_lipschitz_pieces {f : Point → ℝ}
    (S : ℕ → Set Point) (hS : ∀ n, MeasurableSet (S n))
    (hLip : ∀ n, ∀ z ∈ S n, ∀ y, ‖f y - f z‖ ≤ (n : ℝ) * ‖y - z‖)
    (hcover : ∀ᵐ x ∂(volume : Measure Point), ∃ n, x ∈ S n) :
    ∀ᵐ x ∂(volume : Measure Point), DifferentiableAt ℝ f x := by
  have hd : ∀ n, ∀ᵐ x ∂(volume : Measure Point), x ∈ S n → DifferentiableAt ℝ f x := by
    intro n
    have hl : LipschitzOnWith (n : ℝ≥0) f (S n) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [dist_eq_norm, NNReal.coe_natCast] using hLip n y hy x
    filter_upwards [hl.ae_differentiableWithinAt_of_mem, ae_near_set (S n) (hS n)] with x hx hn hxs
    obtain ⟨f', hf'⟩ := hx hxs
    exact (hasFDerivAt_of_within_near_set (by positivity) (hLip n) (hn hxs) hf').differentiableAt
  filter_upwards [ae_all_iff.mpr hd, hcover] with x hx hc
  obtain ⟨n, hn⟩ := hc
  exact hx n hn

def slopePiece (f : Point → ℝ) (m : ℕ) : Set Point :=
  {x | ∀ q : ℚ, 0 < q →
    f (x + ((q : ℝ), (q : ℝ))) - f (x - ((q : ℝ), (q : ℝ))) ≤ m * (q : ℝ)}

theorem measurableSet_slopePiece {f : Point → ℝ} (hf : Measurable f) (m : ℕ) :
    MeasurableSet (slopePiece f m) := by
  simp only [slopePiece, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((hf.comp (measurable_id.add_const _)).sub
    (hf.comp (measurable_id.sub_const _))) measurable_const

theorem monotone_chord_bound {f : Point → ℝ} (hf : Monotone f)
    (x y : Point) (q : ℝ) (hq : ‖y - x‖ ≤ q) :
    ‖f y - f x‖ ≤ f (x + (q, q)) - f (x - (q, q)) := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hq
  have hxy := norm_prod_le_iff.mp hq
  change |y.1 - x.1| ≤ q ∧ |y.2 - x.2| ≤ q at hxy
  rw [abs_le, abs_le] at hxy
  have hlow : x - (q, q) ≤ y := by
    constructor <;> dsimp <;> linarith only [hxy.1.1, hxy.2.1]
  have hup : y ≤ x + (q, q) := by
    constructor <;> dsimp <;> linarith only [hxy.1.2, hxy.2.2]
  have hlowx : x - (q, q) ≤ x := by constructor <;> dsimp <;> linarith
  have hupx : x ≤ x + (q, q) := by constructor <;> dsimp <;> linarith
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [hf hlow, hf hup, hf hlowx, hf hupx]

theorem slopePiece_bound {f : Point → ℝ} (hf : Monotone f) (m : ℕ)
    {x : Point} (hx : x ∈ slopePiece f m) (y : Point) :
    ‖f y - f x‖ ≤ (m : ℝ) * ‖y - x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hm : 0 < (m : ℝ) + 1 := by positivity
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn
    (show ‖y - x‖ < ‖y - x‖ + ε / (m + 1 : ℝ) by linarith only [div_pos hε hm])
  have hq0 : 0 < q := by exact_mod_cast (lt_of_le_of_lt (norm_nonneg _) hq)
  have hh := (monotone_chord_bound hf x y q hq.le).trans (hx q hq0)
  have hq'' : (q : ℝ) - ‖y - x‖ < ε / (m + 1 : ℝ) := by linarith only [hq']
  have hmul := (lt_div_iff₀ hm).mp hq''
  nlinarith only [hh, hmul, hq]

theorem mem_slopePiece_of_diagonal_differentiable {f : Point → ℝ} {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) {x : Point}
    (hd : DifferentiableAt ℝ (fun t : ℝ => f (x + (t, t))) 0) :
    ∃ m, x ∈ slopePiece f m := by
  obtain ⟨C, hC, hc⟩ := hd.hasFDerivAt.isBigO_sub.exists_pos
  obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.mp hc.bound
  obtain ⟨m, hm⟩ := exists_nat_ge (max (2 * C) (2 * B / δ))
  have hmC := (le_max_left (2 * C) (2 * B / δ)).trans hm
  have hmB := (le_max_right (2 * C) (2 * B / δ)).trans hm
  refine ⟨m, ?_⟩
  intro q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  by_cases hqd : (q : ℝ) < δ
  · have hp := hδC (y := (q : ℝ)) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos hq0] using hqd)
    have hn := hδC (y := -(q : ℝ)) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos hq0] using hqd)
    simp only [sub_zero, Real.norm_eq_abs, abs_of_pos hq0, abs_neg] at hp hn
    have he : x + (-(q : ℝ), -(q : ℝ)) = x - ((q : ℝ), (q : ℝ)) := by ext <;> simp [sub_eq_add_neg]
    rw [he] at hn
    have hpu := (abs_le.mp hp).2
    have hnl := (abs_le.mp hn).1
    nlinarith only [hpu, hnl, mul_le_mul_of_nonneg_right hmC hq0.le]
  · have hb1 := (abs_le.mp (show |f (x + ((q : ℝ), (q : ℝ)))| ≤ B by simpa using hb _)).2
    have hb2 := (abs_le.mp (show |f (x - ((q : ℝ), (q : ℝ)))| ≤ B by simpa using hb _)).1
    have hB := (div_le_iff₀ hδ).mp hmB
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hqd) (show 0 ≤ (m : ℝ) by positivity)
    nlinarith only [hb1, hb2, hB, hmul]

theorem bounded_monotone_ae_differentiable {f : Point → ℝ} (hf : Monotone f)
    (hfmeas : Measurable f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂(volume : Measure Point), DifferentiableAt ℝ f x := by
  apply ae_differentiable_of_pointwise_lipschitz_pieces (slopePiece f)
    (measurableSet_slopePiece hfmeas) (fun n z hz y => slopePiece_bound hf n hz y)
  let L : ℝ →ₗ[ℝ] Point := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prod LinearMap.id
  have hS : MeasurableSet {x | ∃ n, x ∈ slopePiece f n} := by
    simpa only [ofPred_exists, Set.ofPred_mem_eq] using
      MeasurableSet.iUnion (measurableSet_slopePiece hfmeas)
  apply ae_mem_of_ae_add_linearMap_mem L volume volume hS
  intro p
  have hg : Monotone (fun t : ℝ => f (p + (t, t))) := by
    intro s t hst
    apply hf
    constructor <;> dsimp <;> linarith only [hst]
  filter_upwards [hg.ae_differentiableAt] with s hs
  apply mem_slopePiece_of_diagonal_differentiable hb
  have hs' : DifferentiableAt ℝ (fun t => f (p + (t, t))) (s + (0 : ℝ)) := by simpa using hs
  have hh := hs'.comp 0 ((differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) 0).const_add s)
  have he : (fun t : ℝ => f (p + L s + (t, t))) =
      (fun t : ℝ => f (p + (t, t))) ∘ (fun t : ℝ => s + t) := by
    funext t
    congr 1
    ext <;> simp [L] <;> ring
  rw [he]
  exact hh

def clampPoint (a b x : Point) : Point :=
  (max a.1 (min b.1 x.1), max a.2 (min b.2 x.2))

lemma clampPoint_mem {a b : Point} (hab : a ≤ b) (x : Point) :
    clampPoint a b x ∈ Icc a b := by
  constructor
  · exact ⟨le_max_left _ _, le_max_left _ _⟩
  · exact ⟨max_le hab.1 (min_le_left _ _), max_le hab.2 (min_le_left _ _)⟩

lemma clampPoint_eq {a b x : Point} (hx : x ∈ Icc a b) : clampPoint a b x = x := by
  ext <;> simp only [clampPoint, min_eq_right, hx.2.1, hx.2.2,
    max_eq_right, hx.1.1, hx.1.2]

lemma clampPoint_monotone (a b : Point) : Monotone (clampPoint a b) := by
  intro x y hxy
  exact ⟨max_le_max le_rfl (min_le_min le_rfl hxy.1),
    max_le_max le_rfl (min_le_min le_rfl hxy.2)⟩

lemma clampPoint_continuous (a b : Point) : Continuous (clampPoint a b) := by
  exact (continuous_const.max (continuous_const.min continuous_fst)).prodMk
    (continuous_const.max (continuous_const.min continuous_snd))

theorem bounded_monotoneOn_Icc_ae_differentiable {f : Point → ℝ} {a b : Point}
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hfmeas : Measurable f)
    {B : ℝ} (hb : ∀ x ∈ Icc a b, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂(volume : Measure Point), x ∈ interior (Icc a b) → DifferentiableAt ℝ f x := by
  let g := fun x => f (clampPoint a b x)
  have hg : Monotone g := fun x y hxy => hf (clampPoint_mem hab x)
    (clampPoint_mem hab y) (clampPoint_monotone a b hxy)
  have hgm : Measurable g := hfmeas.comp (clampPoint_continuous a b).measurable
  filter_upwards [bounded_monotone_ae_differentiable hg hgm
    (fun x => hb _ (clampPoint_mem hab x))] with x hx hxi
  apply hx.congr_of_eventuallyEq
  filter_upwards [mem_interior_iff_mem_nhds.mp hxi] with y hy
  exact congrArg f (clampPoint_eq hy).symm

theorem bounded_monotoneOn_rectangle_ae_differentiable {f : Point → ℝ} {a b : Point}
    (hf : MonotoneOn f (Ioo a.1 b.1 ×ˢ Ioo a.2 b.2)) (hfmeas : Measurable f)
    {B : ℝ} (hb : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂(volume : Measure Point),
      x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 → DifferentiableAt ℝ f x := by
  let castPoint : ℚ × ℚ → Point := fun q => ((q.1 : ℝ), (q.2 : ℝ))
  have hall : ∀ q r : ℚ × ℚ, ∀ᵐ x ∂(volume : Measure Point),
      Icc (castPoint q) (castPoint r) ⊆ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 →
      x ∈ interior (Icc (castPoint q) (castPoint r)) → DifferentiableAt ℝ f x := by
    intro q r
    by_cases hqr : castPoint q ≤ castPoint r
    · by_cases hsub : Icc (castPoint q) (castPoint r) ⊆ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2
      · filter_upwards [bounded_monotoneOn_Icc_ae_differentiable hqr (hf.mono hsub)
          hfmeas (fun x hx => hb x (hsub hx))] with x hx _ hi
        exact hx hi
      · exact Filter.Eventually.of_forall (fun _ h => (hsub h).elim)
    · have hempty : Icc (castPoint q) (castPoint r) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hqr (hx.1.trans hx.2)
      simp only [hempty, interior_empty, mem_empty_iff_false, IsEmpty.forall_iff,
        implies_true, Filter.eventually_true]
  filter_upwards [ae_all_iff.mpr (fun q => ae_all_iff.mpr (hall q))] with x hx hxi
  obtain ⟨q₁, haq₁, hq₁x⟩ := exists_rat_btwn hxi.1.1
  obtain ⟨r₁, hxr₁, hr₁b⟩ := exists_rat_btwn hxi.1.2
  obtain ⟨q₂, haq₂, hq₂x⟩ := exists_rat_btwn hxi.2.1
  obtain ⟨r₂, hxr₂, hr₂b⟩ := exists_rat_btwn hxi.2.2
  apply hx (q₁, q₂) (r₁, r₂)
  · intro y hy
    exact ⟨⟨haq₁.trans_le hy.1.1, hy.2.1.trans_lt hr₁b⟩,
      ⟨haq₂.trans_le hy.1.2, hy.2.2.trans_lt hr₂b⟩⟩
  · rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨hq₁x, hxr₁⟩, ⟨hq₂x, hxr₂⟩⟩

theorem ae_differentiable_linear_change (A : Point ≃L[ℝ] Point) (f : Point → ℝ)
    (U : Set Point)
    (hd : ∀ᵐ x ∂(volume : Measure Point), x ∈ U → DifferentiableAt ℝ (f ∘ A) x) :
    ∀ᵐ y ∂(volume : Measure Point), A.symm y ∈ U → DifferentiableAt ℝ f y := by
  have hA : Measure.QuasiMeasurePreserving A.symm volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume A.symm.toLinearEquiv.toLinearMap
      A.symm.toLinearEquiv.isUnit_det'.ne_zero
  filter_upwards [hA.ae hd] with y hy hyU
  have hh := (hy hyU).comp y (A.symm.differentiable y)
  simpa only [Function.comp_def, A.apply_symm_apply] using hh

end Calculus

end PlanarHalving

end OAI
