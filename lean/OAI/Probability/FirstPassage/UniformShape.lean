import OAI.Probability.FirstPassage.FiniteNet

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable def rescaledPassage (w : Edge → ℝ) (n : ℕ) (v : Plane) : ℝ :=
  passageTime w 0 (latticeFloor ((n : ℝ) • v)) / n

theorem passageTime_origin_difference_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) : |passageTime w 0 p-passageTime w 0 q| ≤ passageTime w p q := by
  have h1 := passageTime_triangle w hw 0 q p
  have h2 := passageTime_triangle w hw 0 p q
  rw [passageTime_symm w hw q p] at h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rescaledPassage_modulus (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4 * (latticeDistance p q : ℝ) + (1 / (k+1 : ℝ)) * n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage w n v-rescaledPassage w n u| ≤ 8 * ‖v-u‖ + ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε/6 by linarith)
  have hthree : Tendsto (fun n : ℕ => 3*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hlarge : ∀ᶠ n : ℕ in atTop, 64/ε < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (64/ε))
  filter_upwards [hthree.eventually (hc k), eventually_ge_atTop 1, hlarge] with n hn hn1 hnlarge
  intro v u hv hu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 64 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp hnlarge
  have hconn := hn (latticeFloor ((n : ℝ) • v)) (latticeFloor_mem_box hv hn1)
    (latticeFloor ((n : ℝ) • u)) (latticeFloor_mem_box hu hn1)
  have hd := latticeDistance_floor_le v u n
  rw [norm_sub_rev] at hd
  have hdiff := passageTime_origin_difference_le w hw (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • u))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hconn
  unfold rescaledPassage
  rw [← sub_div, abs_div, abs_of_pos hnpos]
  apply (div_le_iff₀ hnpos).mpr
  have hk' := mul_lt_mul_of_pos_right hk hnpos
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_rescaledPassage_modulus (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage (fun e => τ e ω) n v-rescaledPassage (fun e => τ e ω) n u| ≤
        8 * ‖v-u‖ + ε := by
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        4 * (latticeDistance p q : ℝ) + (1 / (k+1 : ℝ)) * n := by
    rw [ae_all_iff]
    intro k
    exact ae_eventually_passageTime_connections h (by positivity)
  filter_upwards [h.ae_positive, hc] with ω hp hm
  exact rescaledPassage_modulus _ (fun e => (hp e).le) hm

theorem ae_uniform_rescaledPassage (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage (fun e => τ e ω) n v-μ v| < ε := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Plane
  obtain ⟨B, hB, hBlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  have hp : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Tendsto (fun n : ℕ => rescaledPassage (fun e => τ e ω) n (u i))
        atTop (𝓝 (μ (u i))) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ht (u i)] with ω hω
    exact hω.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, ae_rescaledPassage_modulus h] with ω hp hm
  exact uniform_on_unit_ball_of_dense_limits _ μ u hu B hB hBlip hp hm

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

theorem uniform_rescaled_ball_bound (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage w n v-μ v| < ε)
    (C : ℕ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
      |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*n := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hmul : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply tendsto_atTop.mpr
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

theorem exponential_uniform_shape (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ) :
    ∀ᵐ ω ∂P, UniformShape (fun e => τ e ω) μ := by
  filter_upwards [ae_uniform_rescaledPassage h μ hμ ht] with ω hω
  exact uniformShape_of_uniform_rescaled _ μ hμ hω

end PlanarFPP

end OAI
