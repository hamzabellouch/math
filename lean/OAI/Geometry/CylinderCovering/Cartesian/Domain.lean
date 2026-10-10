import OAI.Geometry.CylinderCovering.Cartesian.DomainDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.Caps
import OAI.Geometry.CylinderCovering.Footprints.Footprints

namespace OAI

open Set MeasureTheory intervalIntegral

namespace CylinderCovering.CartesianCaps

lemma height_lower (τ η y : ℝ) (hη : 0 ≤ η) : 1/2 ≤ height τ η y := by
  unfold height
  have h := mul_nonneg (sq_nonneg τ) (add_nonneg (D_nonneg y) hη)
  linarith

lemma height_upper (τ η y : ℝ) (hη : η ≤ 1) (hy : |y| ≤ 1) :
    height τ η y ≤ 1/2 + (9/4) * τ^2 := by
  have h := mul_le_mul_of_nonneg_left (show D y + η ≤ 9/4 by linarith [D_le y hy]) (sq_nonneg τ)
  unfold height
  linarith

lemma height_le_three_quarters (τ η y : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ≤ 1) (hy : |y| ≤ 1) : height τ η y ≤ 3/4 := by
  have h := height_upper τ η y hη hy
  have hs := small_square τ hτ
  linarith

lemma central_subset_domain (τ η b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ≤ 1) (hb : 3/4 ≤ b) : central τ η ⊆ domain τ η b := by
  rintro ⟨y,s⟩ ⟨hy, hs⟩
  have hya : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  refine ⟨(abs_nonneg y).trans hs.1, ?_, hs.1, hs.2⟩
  exact hs.2.trans ((height_le_three_quarters τ η y hτ hη hya).trans hb)

lemma domain_enclosure (τ η b : ℝ) (hη : η ≤ 1) (hb : b ≤ 1) :
    domain τ η b ⊆ central τ η ∪
      (Icc (-(1/2 + (9/4)*τ^2)) (-1/2) ×ˢ Icc (1/2) (1/2 + (9/4)*τ^2)) ∪
      (Icc (1/2) (1/2 + (9/4)*τ^2) ×ˢ Icc (1/2) (1/2 + (9/4)*τ^2)) := by
  rintro ⟨y,s⟩ ⟨hs0, hsb, hys, hsh⟩
  have hya : |y| ≤ 1 := hys.trans (hsb.trans hb)
  have hsTop : s ≤ 1/2 + (9/4)*τ^2 := hsh.trans (height_upper τ η y hη hya)
  have hyTop : |y| ≤ 1/2 + (9/4)*τ^2 := hys.trans hsTop
  by_cases hy : y ∈ Icc (-1/2 : ℝ) (1/2)
  · exact Or.inl (Or.inl ⟨hy, hys, hsh⟩)
  · rw [mem_Icc, not_and_or] at hy
    rcases hy with hyl | hyr
    · have hyl' : y < -1/2 := lt_of_not_ge hyl
      have hsLow : 1/2 ≤ s := by linarith [neg_le_abs y]
      exact Or.inl (Or.inr ⟨⟨(abs_le.mp hyTop).1, hyl'.le⟩, hsLow, hsTop⟩)
    · have hyr' : 1/2 < y := lt_of_not_ge hyr
      have hsLow : 1/2 ≤ s := by linarith [le_abs_self y]
      exact Or.inr ⟨⟨hyr'.le, (abs_le.mp hyTop).2⟩, hsLow, hsTop⟩

lemma integral_D : (∫ y in (-1/2 : ℝ)..(1/2), D y) = 1/30 := by
  unfold D
  rw [intervalIntegral.integral_add
    ((show Continuous (fun y : ℝ => y^2/4) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun y : ℝ => y^4) by fun_prop).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_div, integral_pow, integral_pow]
  norm_num

lemma integral_abs_half : (∫ y in (-1/2 : ℝ)..(1/2), |y|) = 1/4 := by
  have hc : Continuous (fun y : ℝ => |y|) := continuous_abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1/2) 0) (hc.intervalIntegrable 0 (1/2))]
  have hl : (∫ y in (-1/2 : ℝ)..0, |y|) = ∫ y in (-1/2 : ℝ)..0, -y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 0)] at hy
    exact abs_of_nonpos hy.2
  have hr : (∫ y in (0 : ℝ)..(1/2), |y|) = ∫ y in (0 : ℝ)..(1/2), y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hy
    exact abs_of_nonneg hy.1
  rw [hl, hr, intervalIntegral.integral_neg, integral_id, integral_id]
  norm_num

lemma integral_height (τ η : ℝ) :
    (∫ y in (-1/2 : ℝ)..(1/2), height τ η y) = 1/2 + τ^2 * (1/30 + η) := by
  have hD : Continuous D := by unfold D; fun_prop
  unfold height
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun y => τ^2 * (D y + η)) by fun_prop).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hD.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_D, intervalIntegral.integral_const]
  norm_num [smul_eq_mul]

lemma volume_central (τ η : ℝ) (hη : 0 ≤ η) :
    volume (central τ η) = ENNReal.ofReal (1/4 + τ^2 * (1/30 + η)) := by
  have hh : Continuous (height τ η) := by unfold height D; fun_prop
  unfold central
  rw [Footprints.volume_closedBand_eq_integral continuous_abs hh (by norm_num : (-1/2 : ℝ) ≤ 1/2)
    (by
      intro y hy
      have hya : |y| ≤ 1/2 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
      exact hya.trans (height_lower τ η y hη))]
  rw [intervalIntegral.integral_sub (hh.intervalIntegrable _ _) (continuous_abs.intervalIntegrable _ _),
    integral_height, integral_abs_half]
  congr 1
  ring

lemma volume_rectangle {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) :
    volume (Icc a b ×ˢ Icc c e) = ENNReal.ofReal ((b-a)*(e-c)) := by
  change volume {p : ℝ×ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc c e} = _
  rw [Footprints.volume_closedBand_eq_integral continuous_const continuous_const hab
    (by intro x hx; exact hce)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]

theorem domain_area_bounds (τ η b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Icc (3/4 : ℝ) 1) :
    1/4 + τ^2 * (1/30 + η) ≤ volume.real (domain τ η b) ∧
    volume.real (domain τ η b) ≤ 1/4 + τ^2 * (1/30 + η) + (81/8)*τ^4 := by
  let A : ℝ := 1/4 + τ^2 * (1/30 + η)
  let W : ℝ := (81/16)*τ^4
  let L : Set (ℝ×ℝ) := Icc (-(1/2 + (9/4)*τ^2)) (-1/2) ×ˢ
    Icc (1/2) (1/2 + (9/4)*τ^2)
  let R : Set (ℝ×ℝ) := Icc (1/2) (1/2 + (9/4)*τ^2) ×ˢ
    Icc (1/2) (1/2 + (9/4)*τ^2)
  have hη0 : 0 ≤ η := hη.1.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hCvol : volume (central τ η) = ENNReal.ofReal A := volume_central τ η hη.1.le
  have hLvol : volume L = ENNReal.ofReal W := by
    dsimp [L]
    rw [volume_rectangle (by nlinarith [sq_nonneg τ]) (by nlinarith [sq_nonneg τ])]
    congr 1
    dsimp [W]
    ring
  have hRvol : volume R = ENNReal.ofReal W := by
    dsimp [R]
    rw [volume_rectangle (by nlinarith [sq_nonneg τ]) (by nlinarith [sq_nonneg τ])]
    congr 1
    dsimp [W]
    ring
  have hlow : ENNReal.ofReal A ≤ volume (domain τ η b) := by
    rw [← hCvol]
    exact measure_mono (central_subset_domain τ η b hτ hη.2 hb.1)
  have hup : volume (domain τ η b) ≤ ENNReal.ofReal (A + (81/8)*τ^4) := by
    calc
      volume (domain τ η b) ≤ volume ((central τ η ∪ L) ∪ R) :=
        measure_mono (domain_enclosure τ η b hη.2 hb.2)
      _ ≤ volume (central τ η ∪ L) + volume R := measure_union_le _ _
      _ ≤ (volume (central τ η) + volume L) + volume R :=
        add_le_add (measure_union_le _ _) le_rfl
      _ = (ENNReal.ofReal A + ENNReal.ofReal W) + ENNReal.ofReal W := by rw [hCvol, hLvol, hRvol]
      _ = ENNReal.ofReal ((A+W)+W) := by rw [ENNReal.ofReal_add (add_nonneg hA hW) hW, ENNReal.ofReal_add hA hW]
      _ = ENNReal.ofReal (A + (81/8)*τ^4) := by congr 1; dsimp [W]; ring
  have hfinite : volume (domain τ η b) ≠ ⊤ :=
    (lt_of_le_of_lt hup ENNReal.ofReal_lt_top).ne
  have hlowR := ENNReal.toReal_mono hfinite hlow
  have hupR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
  rw [ENNReal.toReal_ofReal hA] at hlowR
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ A + (81/8)*τ^4)] at hupR
  exact ⟨hlowR, hupR⟩

lemma domain_isClosed (τ η b : ℝ) : IsClosed (domain τ η b) := by
  unfold domain
  change IsClosed ({p : ℝ×ℝ | 0 ≤ p.2} ∩ ({p : ℝ×ℝ | p.2 ≤ b} ∩
    ({p : ℝ×ℝ | |p.1| ≤ p.2} ∩ {p : ℝ×ℝ | p.2 ≤ height τ η p.1})))
  refine (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le (by fun_prop) continuous_snd).inter (isClosed_le continuous_snd ?_)))
  unfold height D
  fun_prop

lemma domain_isCompact (τ η b : ℝ) (hb : b ≤ 1) : IsCompact (domain τ η b) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (domain_isClosed τ η b)
    (show domain τ η b ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from ?_)
  rintro ⟨y,s⟩ ⟨hs0, hsb, hys, hsh⟩
  exact ⟨abs_le.mp (hys.trans (hsb.trans hb)), hs0, hsb.trans hb⟩

lemma domain_radial (τ η b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Icc (3/4 : ℝ) 1) :
    domain τ η b = {p : ℝ×ℝ | ∃ q ∈ Icc (-1 : ℝ) 1,
      ∃ s ∈ Icc (0 : ℝ) (cap τ η q), p = (q*s,s)} := by
  ext p
  rcases p with ⟨y,s⟩
  constructor
  · rintro ⟨hs0, hsb, hys, hsh⟩
    by_cases hs : s = 0
    · have hy : y = 0 := abs_nonpos_iff.mp (by simpa [hs] using hys)
      refine ⟨0, by norm_num, 0, ?_, ?_⟩
      · exact ⟨le_rfl, (cap_mem_unit τ η 0 hτ hη (by norm_num)).1⟩
      · simp [hy, hs]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hq : |y/s| ≤ 1 := by
        rw [abs_div, abs_of_pos hspos]
        exact (div_le_one hspos).2 hys
      have he : (y/s)*s = y := div_mul_cancel₀ y hs
      refine ⟨y/s, abs_le.mp hq, s, ?_, ?_⟩
      · rw [← aperture_eq_Icc τ η b (y/s) hτ hη hb hq]
        exact ⟨hs0, hsb, by simpa [height, he] using hsh⟩
      · simp [he]
  · rintro ⟨q, hq, t, ht, hp⟩
    have haq : |q| ≤ 1 := abs_le.mpr hq
    have ha : t ∈ aperture τ η b q := by
      rw [aperture_eq_Icc τ η b q hτ hη hb haq]
      exact ht
    have hym : |q*t| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht.1]
      simpa using mul_le_mul_of_nonneg_right haq ht.1
    have hcoords : y = q*t ∧ s = t := Prod.mk.inj hp
    rcases hcoords with ⟨rfl,rfl⟩
    exact ⟨ha.1, ha.2.1, hym, ha.2.2⟩

theorem domain_area_expansion (τ η b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Icc (3/4 : ℝ) 1) :
    |volume.real (domain τ η b) - (1/4 + τ^2 * (1/30 + η))| ≤ (81/8)*τ^4 := by
  have h := domain_area_bounds τ η b hτ hη hb
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith [h.2]

lemma untruncated_contains_ray (τ η q : ℝ) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hq : q ≠ 0) : ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℝ, B ≤ s → s ≤ height τ η (q*s) := by
  let K : ℝ := τ^2 * q^4
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨max 1 (1/K), le_max_left _ _, ?_⟩
  intro s hs
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 ≤ s := by linarith
  have hdiv : 1/K ≤ s := (le_max_right _ _).trans hs
  have hKs : 1 ≤ K*s := by
    have h := (div_le_iff₀ hK).1 hdiv
    nlinarith
  have hs2 : 1 ≤ s^2 := by nlinarith
  have hs3 : s ≤ s^3 := by nlinarith [mul_le_mul_of_nonneg_right hs2 hs0]
  have hleading : s ≤ K*s^4 := calc
    s ≤ s^3 := hs3
    _ ≤ (K*s)*s^3 := by simpa using mul_le_mul_of_nonneg_right hKs (show 0 ≤ s^3 by positivity)
    _ = K*s^4 := by ring
  have he : height τ η (q*s) = 1/2 + τ^2*((q*s)^2/4+η) + K*s^4 := by
    unfold height D
    dsimp [K]
    ring
  rw [he]
  have hp : 0 ≤ τ^2*((q*s)^2/4+η) := by positivity
  linarith

lemma untruncated_not_bddAbove (τ η q : ℝ) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hq : q ≠ 0) : ¬ BddAbove {s : ℝ | 0 ≤ s ∧ s ≤ height τ η (q*s)} := by
  obtain ⟨B, hB, htail⟩ := untruncated_contains_ray τ η q hτ hη hq
  rintro ⟨M,hM⟩
  have hBs : B ≤ max B (M+1) := le_max_left _ _
  have h0 : 0 ≤ max B (M+1) := by linarith
  have hle := hM ⟨h0, htail _ hBs⟩
  have hgt : M+1 ≤ max B (M+1) := le_max_right _ _
  linarith

lemma untruncated_gap (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ≤ 1) (hq : |q| ≤ 1) : ¬ 1 ≤ height τ η (q*1) := by
  have h := height_le_three_quarters τ η q hτ hη hq
  simpa only [mul_one] using (show ¬ 1 ≤ height τ η q by linarith)

end CylinderCovering.CartesianCaps

end OAI
