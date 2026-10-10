import OAI.Probability.GammaPassage.RealDirectionGeometry

namespace OAI

namespace GammaFPP.UniformShapeBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory Filter Set Metric
open scoped Topology

theorem latticeFloor_mem_box {v : Plane} {n : ℕ} (hv : ‖v‖ ≤ 2) (hn : 1 ≤ n) :
    latticeFloor ((n : ℝ) • v) ∈ latticeBox (3*n) := by
  have hi (i : Fin 2) : -(3*(n : ℤ)) ≤ ⌊(n : ℝ)*v i⌋ ∧
      ⌊(n : ℝ)*v i⌋ ≤ 3*(n : ℤ) := by
    have ha := (plane_coordinate_le_norm v i).trans hv
    have hb := abs_le.mp ha
    have hl := Int.floor_le ((n : ℝ)*v i)
    have hu := Int.lt_floor_add_one ((n : ℝ)*v i)
    constructor
    · have : -(3*(n : ℝ)) ≤ (⌊(n : ℝ)*v i⌋ : ℝ) := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      exact_mod_cast this
    · have : (⌊(n : ℝ)*v i⌋ : ℝ) ≤ 3*(n : ℝ) := by nlinarith
      exact_mod_cast this
  simpa only [latticeBox, Finset.mem_product, Finset.mem_Icc, latticeFloor,
    PiLp.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using And.intro (hi 0) (hi 1)

theorem latticeDistance_floor_le (v w : Plane) (n : ℕ) :
    (latticeDistance (latticeFloor ((n : ℝ) • v))
      (latticeFloor ((n : ℝ) • w)) : ℝ) ≤ 2 * (n : ℝ) * ‖w-v‖ + 8 := by
  have hd := latticeDistance_le_norm (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • w))
  have he : latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v)) =
      (latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w) +
      (n : ℝ) • (w-v) -
      (latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v) := by
    rw [smul_sub]; abel
  have hb : ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v))‖ ≤
      ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w‖ +
      ‖(n : ℝ) • (w-v)‖ +
      ‖latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_smul, Real.norm_natCast] at hb
  nlinarith [latticeFloor_error ((n : ℝ) • v), latticeFloor_error ((n : ℝ) • w)]

theorem uniform_on_unit_ball_of_dense_limits
    (F : ℕ → Plane → ℝ) (μ : Plane → ℝ) (u : ℕ → Plane) (hu : DenseRange u)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hμ : ∀ v w, |μ v-μ w| ≤ B * ‖v-w‖)
    (hpoint : ∀ i, Tendsto (fun n => F n (u i)) atTop (𝓝 (μ (u i))))
    (hmod : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v w, ‖v‖ ≤ 2 → ‖w‖ ≤ 2 →
      |F n v-F n w| ≤ A * ‖v-w‖ + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v, ‖v‖ ≤ 1 → |F n v-μ v| < ε := by
  intro ε hε
  let δ := min (1/2 : ℝ) (ε / (4*(A+B)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (A+B)*δ ≤ ε/4 := by
    have ht := min_le_right (1/2 : ℝ) (ε/(4*(A+B)))
    dsimp [δ]
    have hmul := (le_div_iff₀ (by linarith : 0 < 4*(A+B))).mp ht
    nlinarith
  have hcover : closedBall (0 : Plane) 1 ⊆ ⋃ i, ball (u i) δ := by
    intro v _
    obtain ⟨i, hi⟩ := hu.exists_dist_lt v hδ
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0 : Plane) 1).elim_finite_subcover
    (fun i => ball (u i) δ) (fun _ => isOpen_ball) hcover
  have hp : ∀ᶠ n in atTop, ∀ i ∈ s, |F n (u i)-μ (u i)| < ε/2 := by
    rw [eventually_all_finset]
    intro i _
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (hpoint i) (ε/2) (by linarith))
  filter_upwards [hp, hmod (ε/4) (by linarith)] with n hn hm
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp (hs (by simpa using hv))
  have hd : ‖v-u i‖ < δ := hvi
  have hui : ‖u i‖ ≤ 2 := by
    have ht := norm_sub_le (u i) v
    have ht' := norm_add_le (u i-v) v
    rw [sub_add_cancel] at ht'
    rw [norm_sub_rev] at ht'
    linarith
  have hm' := hm v (u i) (by linarith) hui
  have hμ' := hμ (u i) v
  rw [norm_sub_rev] at hμ'
  have hp' := hn i hi
  have htri : |F n v-μ v| ≤ |F n v-F n (u i)| +
      |F n (u i)-μ (u i)| + |μ (u i)-μ v| := by
    calc
      _ = |(F n v-F n (u i)) + (F n (u i)-μ (u i)) + (μ (u i)-μ v)| := by
        congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hh := mul_lt_mul_of_pos_left hd (show 0 < A+B by linarith)
  linarith

noncomputable def rescaledPassage (w : Edge → ℝ) (n : ℕ) (v : Plane) : ℝ :=
  passageTime w 0 (latticeFloor ((n : ℝ) • v)) / n

theorem rescaledPassage_lattice_error (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (n : ℕ) (hn : 0 < (n : ℝ)) (z : Vertex) :
    |rescaledPassage w n ((1/(n : ℝ)) • latticeEmbed z) -
      μ ((1/(n : ℝ)) • latticeEmbed z)| =
      |passageTime w 0 z-μ (latticeEmbed z)|/(n : ℝ) := by
  have he : (n : ℝ) • ((1/(n : ℝ)) • latticeEmbed z) = latticeEmbed z := by
    rw [smul_smul, mul_one_div_cancel hn.ne', one_smul]
  rw [rescaledPassage, he, latticeFloor_embed, hμ.homogeneous,
    abs_of_pos (one_div_pos.mpr hn)]
  rw [show (1/(n : ℝ))*μ (latticeEmbed z) = μ (latticeEmbed z)/(n : ℝ) by ring,
    ← sub_div, abs_div, abs_of_pos hn]

/-- Inside-ball version needed in cr:local-travel, at a fixed integer radius
multiplier. Arbitrary fixed positive multipliers are bounded by an integer. -/
theorem uniform_rescaled_ball_bound (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage w n v-μ v| < ε)
    (C : ℕ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
      |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*n := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hmul : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  filter_upwards [hmul.eventually (hu (ε/C) (div_pos hε hCpos)),
    eventually_ge_atTop 1] with n hn hn1
  intro z hz
  have hnpos : (0 : ℝ) < C*n := mul_pos hCpos (by exact_mod_cast (show 0 < n by omega))
  have hcn : (0 : ℝ) < (C*n : ℕ) := by simpa using hnpos
  have hv : ‖(1/((C*n : ℕ) : ℝ)) • latticeEmbed z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hcn)]
    have hz' : ‖latticeEmbed z‖ ≤ ((C*n : ℕ) : ℝ) := by simpa using hz
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using (div_le_one hcn).mpr hz'
  have he := hn _ hv
  rw [rescaledPassage_lattice_error w μ hμ (C*n) hcn z] at he
  have ht := (div_lt_iff₀ hcn).mp he
  have hid : ε/(C : ℝ)*((C*n : ℕ) : ℝ) = ε*n := by
    push_cast
    field_simp
  rw [hid] at ht
  exact ht.le

/-- Uniform shape convergence gives the epsilon-radius estimate for all
lattice endpoints inside a linearly growing ball. -/
def UniformShape (w : Edge → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ z : Vertex, R ≤ ‖latticeEmbed z‖ →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε * ‖latticeEmbed z‖

theorem uniformShape_of_uniform_rescaled (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage w n v-μ v| < ε) : UniformShape w μ := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu (ε/2) (by linarith))
  refine ⟨max 1 (N : ℝ), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro z hz
  let r := ‖latticeEmbed z‖
  let n : ℕ := ⌈r⌉₊
  have hr : 1 ≤ r := (le_max_left _ _).trans hz
  have hnr : r ≤ (n : ℝ) := Nat.le_ceil r
  have hnupper : (n : ℝ) < r+1 := Nat.ceil_lt_add_one (by dsimp [r]; positivity)
  have hnN : N ≤ n := by
    exact_mod_cast ((le_max_right 1 (N : ℝ)).trans hz).trans hnr
  have hnpos : (0 : ℝ) < n := by linarith
  let v : Plane := (1/(n : ℝ)) • latticeEmbed z
  have hnv : (n : ℝ) • v = latticeEmbed z := by
    dsimp [v]
    rw [smul_smul, mul_one_div_cancel hnpos.ne', one_smul]
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnpos)]
    simpa only [r, one_div, div_eq_mul_inv, one_mul, mul_comm] using (div_le_one hnpos).mpr hnr
  have ht := hN n hnN v hv
  have hm : μ (latticeEmbed z) = (n : ℝ) * μ v := by
    rw [← hnv, hμ.homogeneous, abs_of_pos hnpos]
  have hmdiv : μ v = μ (latticeEmbed z)/(n : ℝ) := by
    rw [hm, mul_div_cancel_left₀ _ hnpos.ne']
  simp only [rescaledPassage, hnv, latticeFloor_embed] at ht
  rw [hmdiv, ← sub_div, abs_div, abs_of_pos hnpos] at ht
  have hb := (div_lt_iff₀ hnpos).mp ht
  have hnr2 : (n : ℝ) ≤ 2*r := by linarith
  have he := mul_le_mul_of_nonneg_left hnr2 (show 0 ≤ ε/2 by linarith)
  change |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*r
  linarith

/-- Real-scale inside-ball consequence. This is deterministic and law-free;
ceil only changes the eventually-large scale by at most a factor two. -/
theorem uniform_inside_ball_real_of_integer
    (w : Edge → ℝ) (μ : Plane → ℝ)
    (hu : ∀ C : ℕ, 0 < C → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
      |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ C*s →
      |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*s := by
  obtain ⟨D,hD⟩ := exists_nat_gt C
  have hDpos : 0 < D := by exact_mod_cast (hC.trans hD)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu D hDpos (ε/2) (by linarith))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hs
  intro z hz
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnupper : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hs).trans hsn
  have hbound : ‖latticeEmbed z‖ ≤ (D : ℝ)*n := by
    apply hz.trans
    have h₁ := mul_le_mul_of_nonneg_right hD.le (show 0 ≤ s by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hsn (show (0 : ℝ) ≤ D by positivity)
    exact h₁.trans h₂
  have hb := hN n hnN z hbound
  have hmul := mul_le_mul_of_nonneg_left
    (show (n : ℝ) ≤ 2*s by linarith) (show 0 ≤ ε/2 by linarith)
  linarith

end GammaFPP.UniformShapeBridge

end OAI
