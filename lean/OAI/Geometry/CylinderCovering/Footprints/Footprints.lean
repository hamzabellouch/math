import OAI.Geometry.CylinderCovering.Footprints.QuadraticFootprintsDefinitions

namespace OAI

open MeasureTheory intervalIntegral

namespace CylinderCovering.Footprints

theorem quadraticIntercept_transverse (ε x q c ρ : ℝ) :
    (quadraticIntercept ε x q c ρ).2 - c * (quadraticIntercept ε x q c ρ).1 =
      (q - c) * ρ - ε * x / 2 * (q - c) ^ 2 := by
  dsimp [quadraticIntercept]
  ring

theorem radial_displacement_bound {ε x q c δ : ℝ}
    (hε : 0 ≤ ε) (hx : |x| ≤ 2) (hδ : |q - c| ≤ δ) :
    |ε * x * (q - c)| ≤ 2 * ε * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  calc
    |ε * x * (q - c)| = ε * |x| * |q - c| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hε]
    _ ≤ ε * 2 * δ := by gcongr
    _ = 2 * ε * δ := by ring

theorem transverse_displacement_bound {ε x q c δ : ℝ}
    (hε : 0 ≤ ε) (hx : |x| ≤ 2) (hδ : |q - c| ≤ δ) :
    |ε * x / 2 * (q - c) ^ 2| ≤ ε * δ ^ 2 := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hs : (q - c) ^ 2 ≤ δ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (q - c)) hδ
    simpa only [← sq, sq_abs] using h
  calc
    |ε * x / 2 * (q - c) ^ 2| = ε * |x| / 2 * (q - c) ^ 2 := by
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hε,
        abs_of_nonneg (sq_nonneg (q - c)), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ ε * 2 / 2 * δ ^ 2 := by gcongr
    _ = ε * δ ^ 2 := by ring

theorem quadratic_mem_absolute {ε x q c ρ m M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d) (hqm : |q - m| ≤ d / 2)
    (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) (hA : 2 * ε ≤ A) (hB : ε ≤ B) :
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint m M d A B := by
  have hr := radial_displacement_bound hε hx hqc
  have ht := transverse_displacement_bound hε hx hqc
  have hr' := abs_le.mp hr
  have hAd : 2 * ε * d ≤ A * d := mul_le_mul_of_nonneg_right hA hd
  change -A * d ≤ ρ - ε * x * (q - c) ∧
    ρ - ε * x * (q - c) ≤ M + A * d ∧ _
  refine ⟨by linarith, by linarith, ?_⟩
  let u := ρ - ε * x * (q - c)
  change |q * u + ε * x / 2 * (q - c) ^ 2 - m * u| ≤
    d / 2 * |u| + B * d ^ 2
  calc
    |q * u + ε * x / 2 * (q - c) ^ 2 - m * u| =
      |(q - m) * u + ε * x / 2 * (q - c) ^ 2| := by congr 1; ring
    _ ≤ |(q - m) * u| + |ε * x / 2 * (q - c) ^ 2| := abs_add_le _ _
    _ ≤ d / 2 * |u| + ε * d ^ 2 := by rw [abs_mul]; gcongr
    _ ≤ d / 2 * |u| + B * d ^ 2 := by gcongr

theorem quadratic_mem_absolute_midpoint {ε x q c ρ M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : ε ≤ A) (hB : ε / 4 ≤ B) :
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint c M d A B := by
  have hr := radial_displacement_bound hε hx hqc
  have ht := transverse_displacement_bound hε hx hqc
  have hr' := abs_le.mp hr
  have hAd : ε * d ≤ A * d := mul_le_mul_of_nonneg_right hA hd
  change -A * d ≤ ρ - ε * x * (q - c) ∧
    ρ - ε * x * (q - c) ≤ M + A * d ∧ _
  refine ⟨by linarith, by linarith, ?_⟩
  let u := ρ - ε * x * (q - c)
  change |q * u + ε * x / 2 * (q - c) ^ 2 - c * u| ≤
    d / 2 * |u| + B * d ^ 2
  calc
    |q * u + ε * x / 2 * (q - c) ^ 2 - c * u| =
      |(q - c) * u + ε * x / 2 * (q - c) ^ 2| := by congr 1; ring
    _ ≤ |(q - c) * u| + |ε * x / 2 * (q - c) ^ 2| := abs_add_le _ _
    _ ≤ d / 2 * |u| + ε * (d / 2) ^ 2 := by rw [abs_mul]; gcongr
    _ ≤ d / 2 * |u| + B * d ^ 2 := by
      have := mul_le_mul_of_nonneg_right hB (sq_nonneg d)
      nlinarith

theorem quadratic_mem_affine_midpoint {ε x q c ρ M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : ε ≤ A) (hB : 3 * ε / 4 ≤ B) :
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d A B := by
  have hr := radial_displacement_bound hε hx hqc
  have ht := transverse_displacement_bound hε hx hqc
  have hr' := abs_le.mp hr
  have hAd : ε * d ≤ A * d := mul_le_mul_of_nonneg_right hA hd
  change -A * d ≤ ρ - ε * x * (q - c) ∧
    ρ - ε * x * (q - c) ≤ M + A * d ∧ _
  refine ⟨by linarith, by linarith, ?_⟩
  have hρu : ρ ≤ (quadraticIntercept ε x q c ρ).1 + ε * d := by
    dsimp [quadraticIntercept]
    linarith
  calc
    |(quadraticIntercept ε x q c ρ).2 - c * (quadraticIntercept ε x q c ρ).1| =
      |(q - c) * ρ - ε * x / 2 * (q - c) ^ 2| := by
        rw [quadraticIntercept_transverse]
    _ ≤ |(q - c) * ρ| + |ε * x / 2 * (q - c) ^ 2| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((q - c) * ρ) (-(ε * x / 2 * (q - c) ^ 2))
    _ ≤ d / 2 * ρ + ε * (d / 2) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hρ]
      gcongr
    _ ≤ d / 2 * ((quadraticIntercept ε x q c ρ).1 + ε * d) +
        ε * (d / 2) ^ 2 := by gcongr
    _ ≤ d / 2 * (quadraticIntercept ε x q c ρ).1 + B * d ^ 2 := by
      have := mul_le_mul_of_nonneg_right hB (sq_nonneg d)
      nlinarith

theorem quadratic_mem_endpoint {ε x q c ρ M d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc0 : 0 ≤ q - c) (hqc : q - c ≤ d) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) :
    quadraticIntercept ε x q c ρ ∈ endpointFootprint c M d ε := by
  have hqca : |q - c| ≤ d := by rwa [abs_of_nonneg hqc0]
  have hr := radial_displacement_bound hε hx hqca
  have ht := abs_le.mp (transverse_displacement_bound hε hx hqca)
  have hr' := abs_le.mp hr
  let u := ρ - ε * x * (q - c)
  have hu : -2 * ε * d ≤ u := by dsimp [u]; linarith
  have huM : u ≤ M + 2 * ε * d := by dsimp [u]; linarith
  change -2 * ε * d ≤ u ∧ u ≤ M + 2 * ε * d ∧ _
  refine ⟨hu, huM, ?_⟩
  change -3 * ε * d ^ 2 ≤ q * u + ε * x / 2 * (q - c) ^ 2 - c * u ∧
    q * u + ε * x / 2 * (q - c) ^ 2 - c * u ≤ d * u + 3 * ε * d ^ 2
  have hεd : 0 ≤ ε * d ^ 2 := mul_nonneg hε (sq_nonneg d)
  by_cases hu0 : 0 ≤ u
  · have hprod0 := mul_nonneg hqc0 hu0
    have hprod := mul_le_mul_of_nonneg_right hqc hu0
    constructor <;> nlinarith
  · have hun : u ≤ 0 := le_of_not_ge hu0
    have hprod0 := mul_nonpos_of_nonneg_of_nonpos hqc0 hun
    have hprod := mul_le_mul_of_nonpos_right hqc hun
    have hdu := mul_le_mul_of_nonneg_left hu hd
    constructor <;> nlinarith

theorem integral_affine_width (M d A B : ℝ) :
    (∫ u in (-A * d)..(M + A * d), (d * u + 2 * B * d ^ 2)) =
      affineArea M d A B := by
  rw [intervalIntegral.integral_add
    ((show Continuous (fun u : ℝ => d * u) by fun_prop).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, affineArea]
  ring

theorem integral_absolute_width {M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) :
    (∫ u in (-A * d)..(M + A * d), (d * |u| + 2 * B * d ^ 2)) =
      absoluteArea M d A B := by
  have hleft : -A * d ≤ 0 := by nlinarith [mul_nonneg hA hd]
  have hright : 0 ≤ M + A * d := by positivity
  have hc : Continuous (fun u : ℝ => d * |u| + 2 * B * d ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-A * d) 0) (hc.intervalIntegrable 0 (M + A * d))]
  have hegl : (∫ u in (-A * d)..0, (d * |u| + 2 * B * d ^ 2)) =
      ∫ u in (-A * d)..0, ((-d) * u + 2 * B * d ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hleft] at hu
    dsimp only
    rw [abs_of_nonpos hu.2]
    ring
  have hegr : (∫ u in 0..(M + A * d), (d * |u| + 2 * B * d ^ 2)) =
      ∫ u in 0..(M + A * d), (d * u + 2 * B * d ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hright] at hu
    dsimp only
    rw [abs_of_nonneg hu.1]
  rw [hegl, hegr]
  rw [intervalIntegral.integral_add
    ((show Continuous (fun u : ℝ => (-d) * u) by fun_prop).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    ((show Continuous (fun u : ℝ => d * u) by fun_prop).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul (-d), intervalIntegral.integral_const_mul d]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul, absoluteArea]
  ring

theorem volume_closedBand_eq_integral {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b)
    (hfg : ∀ u ∈ Set.Icc a b, f u ≤ g u) :
    volume {p : ℝ × ℝ | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)} =
      ENNReal.ofReal (∫ u in a..b, (g u - f u)) := by
  classical
  change (volume.prod volume) _ = _
  rw [Measure.prod_apply (measurableSet_region_between_cc
    hf.measurable hg.measurable measurableSet_Icc)]
  have hs : (fun x : ℝ => volume {y : ℝ | x ∈ Set.Icc a b ∧ y ∈ Set.Icc (f x) (g x)}) =
      (Set.Icc a b).indicator (fun x => ENNReal.ofReal (g x - f x)) := by
    funext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · have heq : {y : ℝ | x ∈ Set.Icc a b ∧ y ∈ Set.Icc (f x) (g x)} =
          Set.Icc (f x) (g x) := by ext y; simp only [Set.mem_ofPred_eq, hx, true_and]
      rw [heq, Real.volume_Icc]
    · simp [hx]
  simp only [Set.preimage_ofPred_eq]
  rw [hs, lintegral_indicator measurableSet_Icc]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] (fun u => g u - f u) := by
    change ∀ᵐ u ∂volume.restrict (Set.Icc a b), 0 ≤ g u - f u
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun u hu => sub_nonneg.mpr (hfg u hu))
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun u => g u - f u)
    ((show Continuous (fun u => g u - f u) by fun_prop).integrableOn_Icc) hnonneg]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

theorem volume_absoluteFootprint {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (absoluteFootprint m M d A B) = ENNReal.ofReal (absoluteArea M d A B) := by
  let f := fun u : ℝ => m * u - (d / 2 * |u| + B * d ^ 2)
  let g := fun u : ℝ => m * u + (d / 2 * |u| + B * d ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hrange : -A * d ≤ M + A * d := by nlinarith [mul_nonneg hA hd]
  have hfg : ∀ u ∈ Set.Icc (-A * d) (M + A * d), f u ≤ g u := by
    intro u hu
    dsimp [f, g]
    have : 0 ≤ d / 2 * |u| + B * d ^ 2 := by positivity
    linarith
  have heq : absoluteFootprint m M d A B =
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
        p.2 ∈ Set.Icc (f p.1) (g p.1)} := by
    ext p
    simp only [absoluteFootprint, Set.mem_ofPred_eq, Set.mem_Icc, abs_le, f, g]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, by constructor <;> linarith⟩
  rw [heq, volume_closedBand_eq_integral hf hg hrange hfg]
  have hint : (∫ u in (-A * d)..(M + A * d), (g u - f u)) =
      ∫ u in (-A * d)..(M + A * d), (d * |u| + 2 * B * d ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [f, g]
    ring
  rw [hint, integral_absolute_width hM hd hA]

theorem affine_width_nonneg {d A B u : ℝ} (hd : 0 ≤ d)
    (hAB : A / 2 ≤ B) (hu : -A * d ≤ u) :
    0 ≤ d / 2 * u + B * d ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ d / 2 by positivity)
  have h' := mul_le_mul_of_nonneg_right hAB (sq_nonneg d)
  nlinarith

theorem volume_affineFootprint {c M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hAB : A / 2 ≤ B) :
    volume (affineFootprint c M d A B) = ENNReal.ofReal (affineArea M d A B) := by
  let f := fun u : ℝ => c * u - (d / 2 * u + B * d ^ 2)
  let g := fun u : ℝ => c * u + (d / 2 * u + B * d ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hrange : -A * d ≤ M + A * d := by nlinarith [mul_nonneg hA hd]
  have hfg : ∀ u ∈ Set.Icc (-A * d) (M + A * d), f u ≤ g u := by
    intro u hu
    dsimp [f, g]
    have := affine_width_nonneg hd hAB hu.1
    linarith
  have heq : affineFootprint c M d A B =
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
        p.2 ∈ Set.Icc (f p.1) (g p.1)} := by
    ext p
    simp only [affineFootprint, Set.mem_ofPred_eq, Set.mem_Icc, abs_le, f, g]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, by constructor <;> linarith⟩
  rw [heq, volume_closedBand_eq_integral hf hg hrange hfg]
  have hint : (∫ u in (-A * d)..(M + A * d), (g u - f u)) =
      ∫ u in (-A * d)..(M + A * d), (d * u + 2 * B * d ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [f, g]
    ring
  rw [hint, integral_affine_width]

theorem endpointFootprint_eq_affine (c M d ε : ℝ) :
    endpointFootprint c M d ε = affineFootprint (c + d / 2) M d (2 * ε) (3 * ε) := by
  ext p
  simp only [endpointFootprint, affineFootprint, Set.mem_ofPred_eq, abs_le]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, h2, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, h2, ?_, ?_⟩ <;> nlinarith

theorem volume_endpointFootprint {c M d ε : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hε : 0 ≤ ε) :
    volume (endpointFootprint c M d ε) =
      ENNReal.ofReal (affineArea M d (2 * ε) (3 * ε)) := by
  rw [endpointFootprint_eq_affine]
  exact volume_affineFootprint hM hd (by positivity) (by linarith)

theorem absoluteArea_nonneg {M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ absoluteArea M d A B := by unfold absoluteArea; positivity

theorem affineArea_nonneg {M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ affineArea M d A B := by unfold affineArea; positivity

theorem realVolume_absoluteFootprint {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume.real (absoluteFootprint m M d A B) = absoluteArea M d A B := by
  change (volume (absoluteFootprint m M d A B)).toReal = _
  rw [volume_absoluteFootprint hM hd hA hB,
    ENNReal.toReal_ofReal (absoluteArea_nonneg hM hd hA hB)]

theorem realVolume_affineFootprint {c M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hA : 0 ≤ A) (hAB : A / 2 ≤ B) :
    volume.real (affineFootprint c M d A B) = affineArea M d A B := by
  change (volume (affineFootprint c M d A B)).toReal = _
  rw [volume_affineFootprint hM hd hA hAB,
    ENNReal.toReal_ofReal (affineArea_nonneg hM hd hA (by linarith))]

theorem isCompact_closedBand {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    IsCompact {p : ℝ × ℝ | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)} := by
  obtain ⟨l, hl⟩ := isCompact_Icc.bddBelow_image (f := f) hf.continuousOn
  obtain ⟨r, hr⟩ := isCompact_Icc.bddAbove_image (f := g) hg.continuousOn
  have hc : IsClosed {p : ℝ × ℝ | p.1 ∈ Set.Icc a b ∧
      p.2 ∈ Set.Icc (f p.1) (g p.1)} :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (hf.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (hg.comp continuous_fst)))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
  intro p hp
  refine ⟨hp.1, ?_, ?_⟩
  · exact (hl ⟨p.1, hp.1, rfl⟩).trans hp.2.1
  · exact hp.2.2.trans (hr ⟨p.1, hp.1, rfl⟩)

theorem isCompact_absoluteFootprint (m M d A B : ℝ) :
    IsCompact (absoluteFootprint m M d A B) := by
  have heq : absoluteFootprint m M d A B =
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
        p.2 ∈ Set.Icc (m * p.1 - (d / 2 * |p.1| + B * d ^ 2))
          (m * p.1 + (d / 2 * |p.1| + B * d ^ 2))} := by
    ext p
    simp only [absoluteFootprint, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, by constructor <;> linarith⟩
  rw [heq]
  exact isCompact_closedBand
    (f := fun u => m * u - (d / 2 * |u| + B * d ^ 2))
    (g := fun u => m * u + (d / 2 * |u| + B * d ^ 2))
    (by fun_prop) (by fun_prop) _ _

theorem isCompact_affineFootprint (c M d A B : ℝ) :
    IsCompact (affineFootprint c M d A B) := by
  have heq : affineFootprint c M d A B =
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
        p.2 ∈ Set.Icc (c * p.1 - (d / 2 * p.1 + B * d ^ 2))
          (c * p.1 + (d / 2 * p.1 + B * d ^ 2))} := by
    ext p
    simp only [affineFootprint, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, by constructor <;> linarith⟩
  rw [heq]
  exact isCompact_closedBand
    (f := fun u => c * u - (d / 2 * u + B * d ^ 2))
    (g := fun u => c * u + (d / 2 * u + B * d ^ 2))
    (by fun_prop) (by fun_prop) _ _

theorem isCompact_endpointFootprint (c M d ε : ℝ) :
    IsCompact (endpointFootprint c M d ε) := by
  rw [endpointFootprint_eq_affine]
  exact isCompact_affineFootprint _ _ _ _ _

theorem convex_affineFootprint (c M d A B : ℝ) :
    Convex ℝ (affineFootprint c M d A B) := by
  intro x hx y hy a b ha hb hab
  simp only [affineFootprint, Set.mem_ofPred_eq, abs_le,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  have hea : a * (-A * d) + b * (-A * d) = -A * d := by rw [← add_mul, hab, one_mul]
  have heu : a * (M + A * d) + b * (M + A * d) = M + A * d := by
    rw [← add_mul, hab, one_mul]
  have heB : a * (B * d ^ 2) + b * (B * d ^ 2) = B * d ^ 2 := by
    rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb]
  · linarith [mul_le_mul_of_nonneg_left hx.2.1 ha, mul_le_mul_of_nonneg_left hy.2.1 hb]
  · nlinarith only [mul_le_mul_of_nonneg_left hx.2.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.2.1 hb, heB]
  · nlinarith only [mul_le_mul_of_nonneg_left hx.2.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2.2 hb, heB]

theorem not_convex_absoluteFootprint {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 ≤ B) :
    ¬ Convex ℝ (absoluteFootprint m M d A B) := by
  let t := A * d
  let W := d / 2 * t + B * d ^ 2
  have ht : 0 < t := mul_pos hA hd
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let p : ℝ × ℝ := (-t, -m * t + W)
  let q : ℝ × ℝ := (t, m * t + W)
  have hp : p ∈ absoluteFootprint m M d A B := by
    change -A * d ≤ -t ∧ -t ≤ M + A * d ∧
      |(-m * t + W) - m * (-t)| ≤ d / 2 * |-t| + B * d ^ 2
    refine ⟨by dsimp [t]; ring_nf; rfl, by dsimp [t] at *; nlinarith, ?_⟩
    have he : (-m * t + W) - m * (-t) = W := by ring
    rw [he, abs_of_nonneg hW, abs_neg, abs_of_pos ht]
  have hq : q ∈ absoluteFootprint m M d A B := by
    change -A * d ≤ t ∧ t ≤ M + A * d ∧
      |(m * t + W) - m * t| ≤ d / 2 * |t| + B * d ^ 2
    refine ⟨by dsimp [t] at *; nlinarith, by dsimp [t]; linarith, ?_⟩
    rw [add_sub_cancel_left, abs_of_nonneg hW, abs_of_pos ht]
  intro hc
  have hm := hc.midpoint_mem hp hq
  have he : midpoint ℝ p q = (0, W) := by
    rw [midpoint_eq_smul_add]
    ext <;> simp [p, q, smul_eq_mul]
    ring
  rw [he] at hm
  have hh : |W| ≤ B * d ^ 2 := by
    simpa only [absoluteFootprint, Set.mem_ofPred_eq, mul_zero, sub_zero,
      abs_zero, zero_add] using hm.2.2
  rw [abs_of_nonneg hW] at hh
  have hpos : 0 < d / 2 * t := mul_pos (by positivity) ht
  dsimp [W] at hh
  linarith

theorem absoluteArea_error_bound {M R d A B : ℝ}
    (hM : 0 ≤ M) (hMR : M ≤ R) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ absoluteArea M d A B - d * M ^ 2 / 2 ∧
      absoluteArea M d A B - d * M ^ 2 / 2 ≤
        ((A + 2 * B) * R + (A ^ 2 + 4 * A * B)) * d ^ 2 := by
  have hAB : 0 ≤ A + 2 * B := by positivity
  have hC : 0 ≤ A ^ 2 + 4 * A * B := by positivity
  have hd3 : d ^ 3 ≤ d ^ 2 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd1)]
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR hAB) (sq_nonneg d)
  have hsecond := mul_le_mul_of_nonneg_left hd3 hC
  unfold absoluteArea
  constructor
  · ring_nf
    positivity
  · nlinarith only [hfirst, hsecond]

theorem affineArea_error_bound {M R d A B : ℝ}
    (hM : 0 ≤ M) (hMR : M ≤ R) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ affineArea M d A B - d * M ^ 2 / 2 ∧
      affineArea M d A B - d * M ^ 2 / 2 ≤
        ((A + 2 * B) * R + 4 * A * B) * d ^ 2 := by
  have hAB : 0 ≤ A + 2 * B := by positivity
  have hC : 0 ≤ 4 * A * B := by positivity
  have hd3 : d ^ 3 ≤ d ^ 2 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd1)]
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR hAB) (sq_nonneg d)
  have hsecond := mul_le_mul_of_nonneg_left hd3 hC
  unfold affineArea
  constructor
  · ring_nf
    positivity
  · nlinarith only [hfirst, hsecond]

theorem sum_absoluteArea_error_bound {n : ℕ} {R d A B h : ℝ}
    (M W : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hW : ∀ i, 0 ≤ W i) (hWh : ∀ i, W i ≤ h)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) :
    0 ≤ (∑ i, W i * absoluteArea (M i) d A B) - (∑ i, W i * (d * (M i)^2 / 2)) ∧
      (∑ i, W i * absoluteArea (M i) d A B) - (∑ i, W i * (d * (M i)^2 / 2)) ≤
        (n : ℝ) * h * ((A + 2 * B) * R + (A^2 + 4*A*B)) * d^2 := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  constructor
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hW i)
      (absoluteArea_error_bound (hM i) (hMR i) hd hd1 hA hB).1)
  · calc
      (∑ i, W i * (absoluteArea (M i) d A B - d * (M i)^2 / 2)) ≤
          ∑ _i : Fin n, h * (((A + 2 * B) * R + (A^2 + 4*A*B)) * d^2) := by
        apply Finset.sum_le_sum
        intro i hi
        have he := absoluteArea_error_bound (hM i) (hMR i) hd hd1 hA hB
        exact mul_le_mul (hWh i) he.2 he.1 hh
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem midpoint_table_containment {ε x q c ρ M d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) :
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint c M d ε ε ∧
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d ε (3 * ε / 4) ∧
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d (4 * ε) (4 * ε) ∧
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d ε ε ∧
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d (2 * ε) ε := by
  refine ⟨quadratic_mem_absolute_midpoint hε hd hx hqc hρ hρM le_rfl (by linarith), ?_⟩
  refine ⟨quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM le_rfl le_rfl, ?_⟩
  refine ⟨quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM (by linarith) (by linarith), ?_⟩
  exact ⟨quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM le_rfl (by linarith),
    quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM (by linarith) (by linarith)⟩

theorem generous_absolute_containment {ε x q c ρ m M d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 8) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d) (hqm : |q - m| ≤ d / 2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) :
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint m M d 1 1 ∧
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint m M d
      (Real.sqrt 2 + 2 * ε) (Real.sqrt 2 + 2 * ε) := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  exact ⟨quadratic_mem_absolute hε hd hx hqc hqm hρ hρM (by linarith) (by linarith),
    quadratic_mem_absolute hε hd hx hqc hqm hρ hρM (by linarith) (by linarith)⟩

theorem midpoint_affine_subset_absolute {c M d ε : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε) :
    affineFootprint c M d ε (3 * ε / 4) ⊆ absoluteFootprint c M d ε ε := by
  intro p hp
  refine ⟨hp.1, hp.2.1, hp.2.2.trans ?_⟩
  have hu := mul_le_mul_of_nonneg_left (le_abs_self p.1)
    (show 0 ≤ d / 2 by positivity)
  have he := mul_nonneg hε (sq_nonneg d)
  nlinarith

theorem midpoint_area_difference (M d ε : ℝ) :
    absoluteArea M d ε ε - affineArea M d ε (3 * ε / 4) =
      ε / 2 * M * d ^ 2 + 2 * ε ^ 2 * d ^ 3 := by
  unfold absoluteArea affineArea
  ring

theorem midpoint_affineArea_lt_absoluteArea {M d ε : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hε : 0 < ε) :
    affineArea M d ε (3 * ε / 4) < absoluteArea M d ε ε := by
  have hnonneg : 0 ≤ ε / 2 * M * d ^ 2 := by positivity
  have hpos : 0 < 2 * ε ^ 2 * d ^ 3 := by positivity
  have := midpoint_area_difference M d ε
  linarith

theorem physical_quadratic_intercept (h ε x q c ρ : ℝ) :
    (WithLp.toLp 2 ![x, ρ*q-ε*x*((1+q^2)/2), h*(1-ρ+ε*x*q)] :
      EuclideanSpace ℝ (Fin 3)) -
      x • WithLp.toLp 2 ![1, -ε*((1+c^2)/2), h*ε*c] =
    WithLp.toLp 2 ![0, (quadraticIntercept ε x q c ρ).2,
      h*(1-(quadraticIntercept ε x q c ρ).1)] := by
  ext i
  fin_cases i <;> simp [quadraticIntercept] <;> ring

end CylinderCovering.Footprints

end OAI
