import OAI.Geometry.TranslativeCovering.AllLatticeExclusion

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering

open scoped Classical Topology

lemma isCompact_cube (n : ℕ) (R : ℝ) : IsCompact (cube n R) := by
  have h := (isCompact_pi_infinite (fun _ : Fin n => isCompact_Icc (a := -R) (b := R))).image
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, hx, WithLp.toLp_ofLp 2 x⟩
  · rintro ⟨f, hf, rfl⟩
    exact hf

lemma exists_cube_superset {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ cube n r := by
  obtain ⟨r, hr, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨r, hr, ?_⟩
  intro x hx i
  exact abs_le.mp ((PiLp.norm_apply_le x i).trans (hbound x hx))

def cubePeriod {n : ℕ} (L : ℝ) (z : Fin n → ℤ) : Space n :=
  WithLp.toLp 2 (fun i => 2 * L * (z i : ℝ))

def repeatCube {n : ℕ} (L : ℝ) (S : Set (Space n)) : Set (Space n) :=
  {x | ∃ s ∈ S, ∃ z : Fin n → ℤ, x = s + cubePeriod L z}

lemma cube_cover_mod_period {n : ℕ} {L : ℝ} (hL : 0 < L) (a y : Space n) :
    ∃ z : Fin n → ℤ, y - cubePeriod L z - a ∈ cube n L := by
  let z : Fin n → ℤ := fun i => ⌊(y i - a i + L) / (2 * L)⌋
  refine ⟨z, ?_⟩
  intro i
  have hlo := Int.floor_le ((y i - a i + L) / (2 * L))
  have hhi := Int.lt_floor_add_one ((y i - a i + L) / (2 * L))
  have h2L : 0 < 2 * L := by positivity
  have hlo' := (le_div_iff₀ h2L).mp hlo
  have hhi' := (div_lt_iff₀ h2L).mp hhi
  change -L ≤ y i - 2 * L * (z i : ℝ) - a i ∧
    y i - 2 * L * (z i : ℝ) - a i ≤ L
  change (z i : ℝ) * (2 * L) ≤ y i - a i + L at hlo'
  change y i - a i + L < ((z i : ℝ) + 1) * (2 * L) at hhi'
  constructor <;> linarith

lemma restrict_cover_window {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hKr : K ⊆ cube n r) (hcover : Covers K X) (a : Space n) :
    ∀ y : Space n, y - a ∈ cube n L →
      ∃ x ∈ X ∩ {x | x - a ∈ cube n (L + r)}, y - x ∈ K := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := hcover y
  refine ⟨x, ⟨hx, ?_⟩, hyx⟩
  intro i
  have h1 := hy i
  have h2 := hKr hyx i
  simp only [PiLp.sub_apply] at h1 h2 ⊢
  constructor <;> linarith

lemma periodize_cover {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hL : 0 < L) (hKr : K ⊆ cube n r) (hcover : Covers K X) (a : Space n) :
    Covers K (repeatCube L (X ∩ {x | x - a ∈ cube n (L + r)})) := by
  intro y
  obtain ⟨z, hz⟩ := cube_cover_mod_period hL a y
  obtain ⟨x, hx, hyx⟩ := restrict_cover_window hKr hcover a (y - cubePeriod L z) hz
  refine ⟨x + cubePeriod L z, ⟨x, hx, z, rfl⟩, ?_⟩
  convert hyx using 1; abel

lemma finite_cover_window {n : ℕ} {X : Set (Space n)} (hX : LocallyFiniteCenters X)
    (a : Space n) (R : ℝ) : (X ∩ {x | x - a ∈ cube n R}).Finite := by
  apply hX
  have h := (isCompact_cube n R).image (continuous_id.add (continuous_const (y := a)))
  have heq : (fun y : Space n => y + a) '' cube n R = {x | x - a ∈ cube n R} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_ofPred_eq, add_sub_cancel_right] using hy
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
  change IsCompact ((fun y : Space n => y + a) '' cube n R) at h
  rw [heq] at h
  exact h.isBounded

structure CubicCover {n : ℕ} (K : Set (Space n)) where
  L : ℝ
  positive : 0 < L
  centers : Finset (Space n)
  covers : Covers K (repeatCube L (centers : Set (Space n)))

noncomputable def cubicCenterInfimum {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : CubicCover K,
    (P.centers.card : ℝ≥0∞) / ENNReal.ofReal ((2 * P.L) ^ n)

lemma cubicCenterInfimum_le_window {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hL : 0 < L) (hKr : K ⊆ cube n r) (hX : LocallyFiniteCenters X)
    (hcover : Covers K X) (a : Space n) :
    cubicCenterInfimum K ≤
      ((X ∩ {x | x - a ∈ cube n (L + r)}).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2 * L) ^ n) := by
  let hS := finite_cover_window hX a (L + r)
  let P : CubicCover K :=
    ⟨L, hL, hS.toFinset, by
      simpa only [hS.coe_toFinset] using periodize_cover hL hKr hcover a⟩
  have h := iInf_le (fun P : CubicCover K =>
    (P.centers.card : ℝ≥0∞) / ENNReal.ofReal ((2 * P.L) ^ n)) P
  simpa only [cubicCenterInfimum, P, Set.ncard_eq_toFinset_card _ hS] using h

lemma cubicCenterInfimum_le_upperIntensity {n : ℕ} {K X : Set (Space n)}
    (hK : IsCompact K) (hX : LocallyFiniteCenters X) (hcover : Covers K X) :
    cubicCenterInfimum K ≤ upperCenterIntensity X := by
  obtain ⟨r, hr, hKr⟩ := exists_cube_superset hK
  have hwindow (L : ℝ) (hL : 0 < L) :
      cubicCenterInfimum K ≤ ((X ∩ cube n (L+r)).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2*L)^n) := by
    simpa only [sub_zero, Set.ofPred_mem_eq] using cubicCenterInfimum_le_window hL hKr hX hcover 0
  have hfinite : cubicCenterInfimum K ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (hwindow 1 zero_lt_one)
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  let k := (cubicCenterInfimum K).toReal
  have hsmall (R : ℝ) (hR : r < R) :
      k ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*(R-r))^n) := by
    have h := hwindow (R-r) (sub_pos.mpr hR)
    rw [sub_add_cancel, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_div_of_pos (show 0 < (2*(R-r))^n by positivity)] at h
    have ht := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr h
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*(R-r))^n))] using ht
  have hbound : (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) ≤ᶠ[atTop]
      (fun R : ℝ => ((X ∩ cube n R).ncard : ℝ≥0∞) / ENNReal.ofReal ((2*R)^n)) := by
    filter_upwards [eventually_gt_atTop r] with R hR
    have hR0 : 0 < R := hr.trans hR
    have heq : (1-r/R)*(2*R) = 2*(R-r) := by field_simp
    have hl : k * (1-r/R)^n ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*R)^n) := by
      apply (le_div_iff₀ (show 0 < (2*R)^n by positivity)).mpr
      rw [mul_assoc, ← mul_pow, heq]
      exact (le_div_iff₀ (show 0 < (2*(R-r))^n by positivity)).mp (hsmall R hR)
    have ht := ENNReal.ofReal_le_ofReal hl
    rwa [ENNReal.ofReal_div_of_pos (show 0 < (2*R)^n by positivity),
      ENNReal.ofReal_natCast] at ht
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) atTop
      (𝓝 (cubicCenterInfimum K)) := by
    have hratio : Tendsto (fun R : ℝ => 1-r/R) atTop (𝓝 1) := by
      simpa only [sub_zero, id_eq] using tendsto_const_nhds.sub (tendsto_id.const_div_atTop r)
    have ht := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := k)).mul (hratio.pow n))
    simpa only [one_pow, mul_one, k, ENNReal.ofReal_toReal hfinite] using ht
  calc
    cubicCenterInfimum K = limsup (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) atTop :=
      hlim.limsup_eq.symm
    _ ≤ upperCenterIntensity X := limsup_le_limsup hbound

lemma cubic_density_le_thetaT {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    volume K * cubicCenterInfimum K ≤ thetaT K := by
  apply le_iInf
  intro X
  exact mul_le_mul le_rfl (cubicCenterInfimum_le_upperIntensity hK X.property.1
    X.property.2) bot_le bot_le

noncomputable def integerGrid (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ))

lemma card_integerGrid (n N : ℕ) : (integerGrid n N).card = (2*N+1)^n := by
  simp only [integerGrid, Fintype.card_piFinset, Int.card_Icc]
  have h : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2*N+1 := by omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma repeatCube_window_subset {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    repeatCube L (S : Set (Space n)) ∩ cube n R ⊆
      ((S ×ˢ integerGrid n ⌈(R+r)/(2*L)⌉₊).image
        (fun sz => sz.1 + cubePeriod L sz.2) : Set (Space n)) := by
  intro x hx
  obtain ⟨s, hs, z, rfl⟩ := hx.1
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨(s,z), Finset.mem_product.mpr ⟨hs, ?_⟩, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have h1 := hx.2 i
  have h2 := hS hs i
  change -R ≤ s i + 2*L*(z i : ℝ) ∧ s i + 2*L*(z i : ℝ) ≤ R at h1
  have hceil := Nat.le_ceil ((R+r)/(2*L))
  have hc := (div_le_iff₀ (show 0 < 2*L by positivity)).mp hceil
  have hz : -(⌈(R+r)/(2*L)⌉₊ : ℝ) ≤ (z i : ℝ) ∧
      (z i : ℝ) ≤ (⌈(R+r)/(2*L)⌉₊ : ℝ) := by
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  exact_mod_cast hz

lemma repeatCube_window_finite {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (R : ℝ) : (repeatCube L (S : Set (Space n)) ∩ cube n R).Finite := by
  obtain ⟨r, -, hr⟩ := exists_cube_superset S.finite_toSet.isCompact
  exact (Finset.finite_toSet _).subset (repeatCube_window_subset (R := R) hL S hr)

lemma repeatCube_locallyFinite {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) : LocallyFiniteCenters (repeatCube L (S : Set (Space n))) := by
  intro B hB
  obtain ⟨R, -, hR⟩ := hB.exists_pos_norm_le
  apply (repeatCube_window_finite hL S R).subset
  intro x hx
  exact ⟨hx.1, fun i => abs_le.mp ((PiLp.norm_apply_le x i).trans (hR x hx.2))⟩

lemma repeatCube_count_le {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    (repeatCube L (S : Set (Space n)) ∩ cube n R).ncard ≤ S.card * (2*⌈(R+r)/(2*L)⌉₊+1)^n := by
  have h := Set.ncard_le_ncard (repeatCube_window_subset (R := R) hL S hS)
  rw [Set.ncard_coe_finset] at h
  exact h.trans (Finset.card_image_le.trans_eq (by
    rw [Finset.card_product, card_integerGrid]))

lemma repeatCube_count_le_real {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (hrR : 0 ≤ R+r) (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    ((repeatCube L (S : Set (Space n)) ∩ cube n R).ncard : ℝ) ≤
      (S.card : ℝ) * ((R+r)/L+3)^n := by
  have h := (Nat.cast_le (α := ℝ)).mpr (repeatCube_count_le (R := R) hL S hS)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  have hc := Nat.ceil_lt_add_one (div_nonneg hrR (by positivity : 0 ≤ 2*L))
  have he : 2*((R+r)/(2*L)) = (R+r)/L := by field_simp
  linarith

lemma upperIntensity_repeatCube_le {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) :
    upperCenterIntensity (repeatCube L (S : Set (Space n))) ≤
      (S.card : ℝ≥0∞) / ENNReal.ofReal ((2*L)^n) := by
  obtain ⟨r, hr, hS⟩ := exists_cube_superset S.finite_toSet.isCompact
  let b : ℝ → ℝ := fun R => (S.card : ℝ) * (((R+r)/L+3)/(2*R))^n
  have hb : ∀ᶠ R : ℝ in atTop,
      ((repeatCube L (S : Set (Space n)) ∩ cube n R).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2*R)^n) ≤ ENNReal.ofReal (b R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hcnt := repeatCube_count_le_real hL (by linarith : 0 ≤ R+r) S hS
    have hp : 0 < (2*R)^n := pow_pos (by linarith) _
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hp]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((S.card : ℝ)*((R+r)/L+3)^n)/(2*R)^n :=
        div_le_div_of_nonneg_right hcnt hp.le
      _ = b R := by dsimp [b]; rw [div_pow]; ring
  have hratio : Tendsto (fun R : ℝ => ((R+r)/L+3)/(2*R)) atTop
      (𝓝 (1/(2*L))) := by
    have ht : Tendsto (fun R : ℝ => (1+(r+3*L)/R)/(2*L)) atTop
        (𝓝 (1/(2*L))) := by
      simpa only [add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_id.const_div_atTop (r+3*L))).div_const (2*L)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
    ring
  have ht : Tendsto (fun R => ENNReal.ofReal (b R)) atTop
      (𝓝 ((S.card : ℝ≥0∞)/ENNReal.ofReal ((2*L)^n))) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (S.card : ℝ))).mul (hratio.pow n))
    convert h using 1
    rw [one_div_pow, mul_one_div, ENNReal.ofReal_div_of_pos (pow_pos (by positivity) n)]
    simp only [ENNReal.ofReal_natCast]
  exact (limsup_le_limsup hb).trans_eq ht.limsup_eq

theorem thetaT_eq_cubic {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hvol : volume K ≠ ∞) (hvol0 : volume K ≠ 0) :
    thetaT K = volume K * cubicCenterInfimum K := by
  apply le_antisymm _ (cubic_density_le_thetaT hK)
  rw [cubicCenterInfimum, ENNReal.mul_iInf_of_ne hvol0 hvol]
  apply le_iInf
  intro P
  let X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X} :=
    ⟨repeatCube P.L (P.centers : Set (Space n)),
      repeatCube_locallyFinite P.positive P.centers, P.covers⟩
  exact (iInf_le (fun X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X} =>
    volume K * upperCenterIntensity X.val) X).trans
      (mul_le_mul le_rfl (upperIntensity_repeatCube_le P.positive P.centers) bot_le bot_le)

theorem periodization {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K = volume K * cubicCenterInfimum K := by
  apply thetaT_eq_cubic hK.1 hK.1.measure_lt_top.ne
  exact ne_of_gt ((isOpen_interior.measure_pos volume hK.2.2).trans_le
    (measure_mono interior_subset))

end TranslativeCovering

end OAI
