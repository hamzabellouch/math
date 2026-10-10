import OAI.Combinatorics.HalvingLines.Rigidity

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma LineControl.between_chord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E → E} {v : E} (C : LineControl f v)
    (n : ℕ) (x : E) (a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖f n (x + t • v) - f n (x + a • v)‖ ≤
      (C.constant * ‖C.level‖) * ‖f n (x + b • v) - f n (x + a • v)‖ := by
  have h₁ := (C.strict n x).monotone hat
  have h₂ := (C.strict n x).monotone htb
  simp only [map_sub] at h₁ h₂
  have hz : 0 ≤ C.level (f n (x + t • v) - f n (x + a • v)) := by
    rw [map_sub]
    linarith only [h₁]
  have hle : C.level (f n (x + t • v) - f n (x + a • v)) ≤
      C.level (f n (x + b • v) - f n (x + a • v)) := by
    rw [map_sub, map_sub]
    linarith only [h₂]
  calc
    _ ≤ C.constant * |C.level (f n (x + t • v) - f n (x + a • v))| := C.chord n x t a
    _ ≤ C.constant * (C.level (f n (x + b • v) - f n (x + a • v))) := by
      rw [abs_of_nonneg hz]
      exact mul_le_mul_of_nonneg_left hle C.constant.coe_nonneg
    _ ≤ C.constant * (‖C.level‖ * ‖f n (x + b • v) - f n (x + a • v)‖) := by
      apply mul_le_mul_of_nonneg_left _ C.constant.coe_nonneg
      exact (le_abs_self _).trans (C.level.le_opNorm _)
    _ = _ := by ring

lemma FoliatedSequence.axis_bounded (F : FoliatedSequence) (σ t : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ B : ℝ, ∀ n, ‖F.map n (t, 0)‖ ≤ B := by
  obtain ⟨A, _, hA⟩ := (Metric.isBounded_range_of_tendsto _ hzero).exists_pos_norm_le
  obtain ⟨B, _, hB⟩ := (Metric.isBounded_range_of_tendsto _ hone).exists_pos_norm_le
  let C := F.control .horizontal
  refine ⟨(C.constant * ‖C.level‖) * (B + A) + A, fun n => ?_⟩
  have hh := C.between_chord n 0 0 t 1 ht₀ ht₁
  simp only [Foliation.direction, zero_smul, zero_add, one_smul,
    Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at hh
  have hA' := hA _ (Set.mem_range_self n)
  have hB' := hB _ (Set.mem_range_self n)
  calc
    ‖F.map n (t, 0)‖ ≤ ‖F.map n (t, 0) - F.map n 0‖ + ‖F.map n 0‖ := norm_le_norm_sub_add _ _
    _ ≤ (C.constant * ‖C.level‖) * ‖F.map n (1, 0) - F.map n 0‖ + A := add_le_add hh hA'
    _ ≤ (C.constant * ‖C.level‖) * (B + A) + A := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg C.constant.coe_nonneg (norm_nonneg _))
      exact (norm_sub_le _ _).trans (add_le_add hB' hA')

lemma FoliatedSequence.good_reciprocal (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (m : ℕ) (hm : 0 < m) : F.Good σ ((m : ℝ)⁻¹, 0) := by
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨B, hB⟩ := F.axis_bounded σ ((m : ℝ)⁻¹) hzero hone
    (inv_nonneg.mpr hm₀.le) (inv_le_one_of_one_le₀ hm₁)
  apply (isCompact_closedBall (0 : Point) B).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun n => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB n))
  intro b _ hcluster
  obtain ⟨ρ, hρ, hb⟩ := hcluster.tendsto_subseq
  have hz : Tendsto (fun n => F.map (ρ n) 0) atTop (𝓝 (0 : Point)) := by
    simpa only [Good, Function.comp_def, smul_zero] using hzero.comp hρ.tendsto_atTop
  obtain ⟨r, hr⟩ := F.direction .horizontal ρ hρ (fun _ => 0)
    (fun _ => ((m : ℝ)⁻¹, 0))
    (fun _ => ⟨(m : ℝ)⁻¹, by simp [Foliation.direction]⟩) 0 b hz hb
  have hb' : b = (r, 0) := by simpa [Foliation.direction] using hr
  let G := F.subseq ρ hρ
  have hgzero : G.Good (r * m) 0 := by simpa only [Good, G, subseq, smul_zero] using hz
  have hgseed : G.Good (r * m) ((m : ℝ)⁻¹, 0) := by
    have he : (r * m) • (((m : ℝ)⁻¹, 0) : Point) = b := by
      rw [hb']
      ext <;> simp [ne_of_gt hm₀]
    simpa only [Good, he, G, subseq, Function.comp_def] using hb
  have hg := G.good_nat_axis (r * m) ((m : ℝ)⁻¹) hgzero hgseed m
  have hg' : G.Good (r * m) (1, 0) := by simpa only [mul_inv_cancel₀ (ne_of_gt hm₀)] using hg
  have he : (r * m) • ((1, 0) : Point) = σ • ((1, 0) : Point) :=
    tendsto_nhds_unique hg' (hone.subseq ρ hρ)
  have he' : r * m = σ := by simpa using congrArg Prod.fst he
  rw [hb', ← he']
  ext <;> simp [ne_of_gt hm₀]

lemma FoliatedSequence.good_rational_grid (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (m : ℕ) (hm : 0 < m) (a b : ℤ) :
    F.Good σ ((a : ℝ) / m, (b : ℝ) / m) := by
  simpa only [div_eq_mul_inv] using
    F.good_lattice σ ((m : ℝ)⁻¹) hzero (F.good_reciprocal σ hzero hone m hm) a b

noncomputable def FoliatedSequence.axisConstant (F : FoliatedSequence) (i : Foliation) : ℝ :=
  (F.control i).constant * ‖(F.control i).level‖

lemma FoliatedSequence.axisConstant_nonneg (F : FoliatedSequence) (i : Foliation) :
    0 ≤ F.axisConstant i := mul_nonneg (F.control i).constant.coe_nonneg (norm_nonneg _)

noncomputable def FoliatedSequence.rectConstant (F : FoliatedSequence) : ℝ :=
  F.axisConstant .horizontal * (2 * F.axisConstant .vertical + 1) + F.axisConstant .vertical

lemma FoliatedSequence.rectConstant_nonneg (F : FoliatedSequence) : 0 ≤ F.rectConstant := by
  unfold rectConstant
  have hh := F.axisConstant_nonneg .horizontal
  have hv := F.axisConstant_nonneg .vertical
  positivity

lemma FoliatedSequence.horizontal_between (F : FoliatedSequence) (n : ℕ)
    (a t b y : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖F.map n (t, y) - F.map n (a, y)‖ ≤
      F.axisConstant .horizontal * ‖F.map n (b, y) - F.map n (a, y)‖ := by
  simpa [Foliation.direction, axisConstant] using
    (F.control .horizontal).between_chord n (0, y) a t b hat htb

lemma FoliatedSequence.vertical_between (F : FoliatedSequence) (n : ℕ)
    (a t b x : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖F.map n (x, t) - F.map n (x, a)‖ ≤
      F.axisConstant .vertical * ‖F.map n (x, b) - F.map n (x, a)‖ := by
  simpa [Foliation.direction, axisConstant] using
    (F.control .vertical).between_chord n (x, 0) a t b hat htb

lemma FoliatedSequence.rectangle_chord (F : FoliatedSequence) (n : ℕ)
    (a b c d q : ℝ) (x : Point) (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hbottom : ‖F.map n (b, c) - F.map n (a, c)‖ ≤ q)
    (hleft : ‖F.map n (a, d) - F.map n (a, c)‖ ≤ q)
    (hright : ‖F.map n (b, d) - F.map n (b, c)‖ ≤ q) :
    ‖F.map n x - F.map n (a, c)‖ ≤ F.rectConstant * q := by
  let H := F.axisConstant .horizontal
  let V := F.axisConstant .vertical
  have hH : 0 ≤ H := F.axisConstant_nonneg _
  have hV : 0 ≤ V := F.axisConstant_nonneg _
  have hl : ‖F.map n (a, x.2) - F.map n (a, c)‖ ≤ V * q :=
    (F.vertical_between n c x.2 d a hy.1 hy.2).trans (mul_le_mul_of_nonneg_left hleft hV)
  have hr : ‖F.map n (b, x.2) - F.map n (b, c)‖ ≤ V * q :=
    (F.vertical_between n c x.2 d b hy.1 hy.2).trans (mul_le_mul_of_nonneg_left hright hV)
  have hb : ‖F.map n (b, x.2) - F.map n (a, x.2)‖ ≤ V * q + q + V * q := by
    calc
      _ ≤ ‖F.map n (b, x.2) - F.map n (b, c)‖ +
        ‖F.map n (b, c) - F.map n (a, c)‖ +
        ‖F.map n (a, c) - F.map n (a, x.2)‖ := by
          have h₁ := dist_triangle (F.map n (b, x.2)) (F.map n (b, c)) (F.map n (a, c))
          have h₂ := dist_triangle (F.map n (b, x.2)) (F.map n (a, c)) (F.map n (a, x.2))
          simp only [dist_eq_norm] at h₁ h₂
          linarith only [h₁, h₂]
      _ ≤ _ := add_le_add (add_le_add hr hbottom) (by rwa [norm_sub_rev])
  have ht : ‖F.map n x - F.map n (a, x.2)‖ ≤ H * (V * q + q + V * q) :=
    (F.horizontal_between n a x.1 b x.2 hx.1 hx.2).trans (mul_le_mul_of_nonneg_left hb hH)
  calc
    _ ≤ ‖F.map n x - F.map n (a, x.2)‖ + ‖F.map n (a, x.2) - F.map n (a, c)‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (F.map n x) (F.map n (a, x.2)) (F.map n (a, c))
    _ ≤ H * (V * q + q + V * q) + V * q := add_le_add ht hl
    _ = _ := by dsimp [H, V, rectConstant]; ring

lemma norm_rectangle_corner (a b c d δ : ℝ) (x : Point)
    (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hab : b - a ≤ δ) (hcd : d - c ≤ δ) : ‖x - (a, c)‖ ≤ δ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change |x.1 - a| ≤ δ
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith only [hx.2, hab]
  · change |x.2 - c| ≤ δ
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    linarith only [hy.2, hcd]

lemma norm_image_edge (f : Point → Point) (σ δ : ℝ) (x y : Point)
    (hx : ‖f x - σ • x‖ ≤ δ) (hy : ‖f y - σ • y‖ ≤ δ)
    (hxy : ‖x - y‖ ≤ δ) : ‖f x - f y‖ ≤ (2 + |σ|) * δ := by
  have h := dist_triangle (f x) (σ • x) (σ • y)
  have h' := dist_triangle (f x) (σ • y) (f y)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs] at h h'
  rw [norm_sub_rev (σ • y)] at h'
  have hh := mul_le_mul_of_nonneg_left hxy (abs_nonneg σ)
  nlinarith only [h, h', hx, hy, hh]

lemma FoliatedSequence.rectangle_error (F : FoliatedSequence) (n : ℕ)
    (σ a b c d δ : ℝ) (x : Point) (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hab : b - a ≤ δ) (hcd : d - c ≤ δ)
    (h₀₀ : ‖F.map n (a, c) - σ • (a, c)‖ ≤ δ)
    (h₁₀ : ‖F.map n (b, c) - σ • (b, c)‖ ≤ δ)
    (h₀₁ : ‖F.map n (a, d) - σ • (a, d)‖ ≤ δ)
    (h₁₁ : ‖F.map n (b, d) - σ • (b, d)‖ ≤ δ) :
    ‖F.map n x - σ • x‖ ≤ (F.rectConstant * (2 + |σ|) + 1 + |σ|) * δ := by
  have ha : a ≤ b := hx.1.trans hx.2
  have hc : c ≤ d := hy.1.trans hy.2
  have hh := F.rectangle_chord n a b c d ((2 + |σ|) * δ) x hx hy
    (norm_image_edge _ σ δ _ _ h₁₀ h₀₀
      (norm_rectangle_corner a b c d δ (b, c) ⟨ha, le_rfl⟩ ⟨le_rfl, hc⟩ hab hcd))
    (norm_image_edge _ σ δ _ _ h₀₁ h₀₀
      (norm_rectangle_corner a b c d δ (a, d) ⟨le_rfl, ha⟩ ⟨hc, le_rfl⟩ hab hcd))
    (norm_image_edge _ σ δ _ _ h₁₁ h₁₀
      (norm_rectangle_corner b b c d δ (b, d) ⟨le_rfl, le_rfl⟩ ⟨hc, le_rfl⟩
        (by linarith only [ha, hab]) hcd))
  have hnorm := norm_rectangle_corner a b c d δ x hx hy hab hcd
  have h₁ := dist_triangle (F.map n x) (F.map n (a, c)) (σ • (a, c))
  have h₂ := dist_triangle (F.map n x) (σ • (a, c)) (σ • x)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs] at h₁ h₂
  rw [norm_sub_rev (a, c)] at h₂
  have hh' := mul_le_mul_of_nonneg_left hnorm (abs_nonneg σ)
  nlinarith only [hh, h₀₀, h₁, h₂, hh']

lemma FoliatedSequence.small_good_rectangle (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0)) (x : Point) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a b c d : ℝ, a < x.1 ∧ x.1 < b ∧ c < x.2 ∧ x.2 < d ∧
      b - a ≤ δ ∧ d - c ≤ δ ∧ F.Good σ (a, c) ∧ F.Good σ (b, c) ∧
        F.Good σ (a, d) ∧ F.Good σ (b, d) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ)
  have hmR : (0 : ℝ) < m := (div_pos (by norm_num) hδ).trans hm
  have hmN : 0 < m := Nat.cast_pos.mp hmR
  let i : ℤ := ⌊(m : ℝ) * x.1⌋
  let j : ℤ := ⌊(m : ℝ) * x.2⌋
  have hi₀ : (i : ℝ) ≤ m * x.1 := Int.floor_le _
  have hi₁ : m * x.1 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hj₀ : (j : ℝ) ≤ m * x.2 := Int.floor_le _
  have hj₁ : m * x.2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hmesh : 2 / (m : ℝ) < δ := by
    exact (div_lt_iff₀ hmR).mpr (by nlinarith only [(div_lt_iff₀ hδ).mp hm])
  refine ⟨((i - 1 : ℤ) : ℝ) / m, ((i + 1 : ℤ) : ℝ) / m,
    ((j - 1 : ℤ) : ℝ) / m, ((j + 1 : ℤ) : ℝ) / m, ?_, ?_, ?_, ?_, ?_, ?_,
    F.good_rational_grid σ hzero hone m hmN (i - 1) (j - 1),
    F.good_rational_grid σ hzero hone m hmN (i + 1) (j - 1),
    F.good_rational_grid σ hzero hone m hmN (i - 1) (j + 1),
    F.good_rational_grid σ hzero hone m hmN (i + 1) (j + 1)⟩
  · rw [div_lt_iff₀ hmR]
    push_cast
    linarith only [hi₀]
  · rw [lt_div_iff₀ hmR]
    push_cast
    linarith only [hi₁]
  · rw [div_lt_iff₀ hmR]
    push_cast
    linarith only [hj₀]
  · rw [lt_div_iff₀ hmR]
    push_cast
    linarith only [hj₁]
  · have he : (((i + 1 : ℤ) : ℝ) / m - ((i - 1 : ℤ) : ℝ) / m) = 2 / (m : ℝ) := by
      push_cast
      ring
    rw [he]
    exact hmesh.le
  · have he : (((j + 1 : ℤ) : ℝ) / m - ((j - 1 : ℤ) : ℝ) / m) = 2 / (m : ℝ) := by
      push_cast
      ring
    rw [he]
    exact hmesh.le

lemma FoliatedSequence.good_eventual_error (F : FoliatedSequence) (σ : ℝ)
    (x : Point) (hx : F.Good σ x) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ‖F.map n x - σ • x‖ ≤ δ := by
  exact (Metric.tendsto_nhds.mp hx δ hδ).mono fun n hn => by
    simpa only [dist_eq_norm] using hn.le

lemma FoliatedSequence.locally_uniform (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0)) :
    TendstoLocallyUniformly (fun n => F.map n) (fun x => σ • x) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let L : ℝ := F.rectConstant * (2 + |σ|) + 1 + |σ|
  have hL : 0 ≤ L := by
    have hc := F.rectConstant_nonneg
    dsimp [L]
    positivity
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < L + 1)).mpr
    nlinarith only [hε]
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hg₀₀, hg₁₀, hg₀₁, hg₁₁⟩ :=
    F.small_good_rectangle σ hzero hone x δ hδ
  refine ⟨{y : Point | y.1 ∈ Set.Ioo a b ∧ y.2 ∈ Set.Ioo c d}, ?_, ?_⟩
  · exact ((isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_Ioo.preimage continuous_snd)).mem_nhds ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
  · filter_upwards [F.good_eventual_error σ _ hg₀₀ δ hδ,
      F.good_eventual_error σ _ hg₁₀ δ hδ, F.good_eventual_error σ _ hg₀₁ δ hδ,
      F.good_eventual_error σ _ hg₁₁ δ hδ] with n h₀₀ h₁₀ h₀₁ h₁₁
    intro y hy
    rw [dist_eq_norm, norm_sub_rev]
    exact (F.rectangle_error n σ a b c d δ y ⟨hy.1.1.le, hy.1.2.le⟩
      ⟨hy.2.1.le, hy.2.2.le⟩ hab hcd h₀₀ h₁₀ h₀₁ h₁₁).trans_lt hsmall

lemma FoliatedSequence.uniform_on_compact (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (K : Set Point) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => F.map n) (fun x => σ • x) atTop K := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((F.locally_uniform σ hzero hone).tendstoLocallyUniformlyOn)

lemma inverse_bound_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (σ : ℝ) (hσ : |σ| = 1)
    (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ = r → ‖f x - σ • x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y‖ < r := by
  have hinv₀ : f.symm 0 = 0 := by
    calc
      f.symm 0 = f.symm (f 0) := congrArg f.symm hz.symm
      _ = 0 := f.left_inv (by rw [hrange]; trivial)
  have hsmul (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • y‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans hy
  have hpath : Set.MapsTo (fun t : ℝ => t • y) (Set.Icc 0 1) f.target := by
    intro t ht
    exact htarget (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmul t ht)
  apply path_stays_inside f (fun t : ℝ => f.symm (t • y)) (f.symm y) r (r - ε)
    (by linarith)
    (f.continuousOn_symm.comp (continuous_id.smul continuous_const).continuousOn hpath)
  · simpa only [zero_smul] using hinv₀
  · simp only [one_smul]
  · intro t ht
    rw [f.right_inv (hpath ht)]
    have hb := hsmul t ht
    linarith only [hb, hgap]
  · intro x hx
    have he := hnear x hx
    have hb : ‖x‖ ≤ ‖f x - σ • x‖ + ‖f x‖ := by
      calc
        ‖x‖ = ‖σ • x‖ := by rw [norm_smul, Real.norm_eq_abs, hσ, one_mul]
        _ ≤ ‖σ • x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
        _ = _ := by rw [norm_sub_rev]
    linarith only [hx, he, hb]

lemma norm_sign_inverse_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x y : E) :
    ‖x - σ • y‖ = ‖y - σ • x‖ := by
  rcases hσ with rfl | rfl
  · simpa only [one_smul] using norm_sub_rev x y
  · simp only [neg_one_smul, sub_neg_eq_add, add_comm]

lemma inverse_near_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ ≤ r → ‖f x - σ • x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y - σ • y‖ ≤ ε := by
  have hyT : y ∈ f.target := htarget (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
  have hσ' : |σ| = 1 := (abs_eq (by norm_num)).mpr hσ
  have hb := inverse_bound_sign f hrange hz σ hσ' R r ε hR hε hgap htarget
    (fun x hx => hnear x hx.le) y hy
  have he := hnear (f.symm y) hb.le
  rw [f.right_inv hyT] at he
  rwa [norm_sign_inverse_error σ hσ]

lemma FoliatedSequence.inverse_uniform_on_compact (F : FoliatedSequence) (σ : ℝ)
    (hz : ∀ n, F.map n 0 = 0) (hσ : σ = 1 ∨ σ = -1)
    (hone : F.Good σ (1, 0)) (K : Set Point) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => (F.map n).symm) (fun x => σ • x) atTop K := by
  have hzero : F.Good σ 0 := by
    simpa only [Good, hz, smul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Point)) atTop (𝓝 0))
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hK.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : K ⊆ Metric.closedBall (0 : Point) R := hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hu := F.uniform_on_compact σ hzero hone (Metric.closedBall 0 (R + ε + 1))
    (isCompact_closedBall _ _)
  filter_upwards [F.exhaust (Metric.closedBall 0 R) (isCompact_closedBall _ _),
    (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (by positivity))] with n htarget hn
  intro y hy
  rw [dist_eq_norm, norm_sub_rev]
  have hnear (x : Point) (hx : ‖x‖ ≤ R + ε + 1) : ‖F.map n x - σ • x‖ ≤ ε / 2 := by
    have hh := hn x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    simpa only [dist_eq_norm, norm_sub_rev] using hh.le
  have hy' : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hy
  exact (inverse_near_sign (F.map n) (F.source n) (hz n) σ hσ R (R + ε + 1) (ε / 2)
    hR (by positivity) (by linarith only [hε]) htarget hnear y hy').trans_lt (by linarith only [hε])

theorem FoliatedSequence.normalized_compactness (F : FoliatedSequence)
    (hz : ∀ n, F.map n 0 = 0) (hone : ∀ n, ‖F.map n (1, 0)‖ = 1) :
    ∃ (ρ : ℕ → ℕ), StrictMono ρ ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ K : Set Point, IsCompact K →
        TendstoUniformlyOn (fun n => F.map (ρ n)) (fun x => σ • x) atTop K) ∧
      (∀ K : Set Point, IsCompact K →
        TendstoUniformlyOn (fun n => (F.map (ρ n)).symm) (fun x => σ • x) atTop K) := by
  obtain ⟨b, hb, ρ, hρ, hlim⟩ := (isCompact_sphere (0 : Point) 1).tendsto_subseq
    (fun n => by simpa only [Metric.mem_sphere, dist_zero_right] using hone n)
  have hzero : Tendsto (fun n => F.map (ρ n) 0) atTop (𝓝 (0 : Point)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Point)) atTop (𝓝 0))
  obtain ⟨σ, hσb⟩ := F.direction .horizontal ρ hρ (fun _ => 0) (fun _ => (1, 0))
    (fun _ => ⟨1, by simp [Foliation.direction]⟩) 0 b hzero hlim
  have hb' : b = (σ, 0) := by simpa [Foliation.direction] using hσb
  have hσ : σ = 1 ∨ σ = -1 := by
    apply (abs_eq (by norm_num)).mp
    simpa [hb', Metric.mem_sphere, Prod.norm_def] using hb
  let G := F.subseq ρ hρ
  have hgzero : G.Good σ 0 := by simpa only [Good, G, subseq, smul_zero] using hzero
  have hgone : G.Good σ (1, 0) := by
    simpa [Good, G, subseq, Function.comp_def, hb'] using hlim
  exact ⟨ρ, hρ, σ, hσ, G.uniform_on_compact σ hgzero hgone,
    G.inverse_uniform_on_compact σ (fun n => hz (ρ n)) hσ hgone⟩

end Zoom

end PlanarHalving

end OAI
