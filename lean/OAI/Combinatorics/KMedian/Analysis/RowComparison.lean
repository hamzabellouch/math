import Mathlib
import OAI.Combinatorics.KMedian.Analysis.FiniteAverages

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

theorem positive_row_location {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z h : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t)
    (hF : 0 < rowValue π Z q p m a z b s D R) :
    0 < average π q ∧ 0 < G p m a z b s (average π q) ∧ d s < D := by
  have hr := average_unit_bounds hπ0 hπ hq0 hq
  have hrpos : 0 < average π q := by
    by_contra! hn
    have he : average π q = 0 := le_antisymm hn hr.1
    have hrate := rate_comparison hπ0 hπ hZ sb.p_nonneg sb.p_le_half hD hZ0 hq0 hq hcomp
    rw [he, sub_zero, one_mul] at hrate
    have h₁ := mul_le_mul_of_nonneg_left hrate (C_pos sb.p_le_half s).le
    have h₂ : 0 ≤ average π (fun t => (1 - q t) * max (Z t - a * D) 0) :=
      average_nonneg hπ0 (fun t => mul_nonneg (sub_nonneg.mpr (hq t)) (le_max_right _ _))
    have h₃ := mul_nonneg (show 0 ≤ (2 / 5 : ℝ) * D + 8 / 5 by linarith)
      sb.z_nonneg
    unfold rowValue at hF
    rw [he] at hF
    nlinarith only [hF, h₁, h₂, h₃]
  have hlin := sb.linear s (average π q) hr.1 hr.2
  have hmaj := row_le_linear (m := m) (a := a) (z := z) (b := b) (s := s)
    hπ0 hπ hZ sb.p_nonneg sb.p_le_half hD hZ0 hq0 hq hcomp
  have hKG : K p z b s (average π q) < D * G p m a z b s (average π q) := by
    linarith
  have hG : 0 < G p m a z b s (average π q) := by
    by_contra! hn
    have ht := mul_nonpos_of_nonneg_of_nonpos hD hn
    linarith [hlin.2.1]
  refine ⟨hrpos, hG, ?_⟩
  have ht := hlin.2.2.trans_lt hKG
  nlinarith only [ht, hG]

theorem d_lower (s : Bool) : (2 / 5 : ℝ) ≤ d s := by cases s <;> norm_num [d]

theorem H_bounds {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) : 0 ≤ H h s ∧ H h s ≤ 197 / 500 := by
  cases s
  · exact ⟨sb.h_nonneg, sb.h_le⟩
  · norm_num [H]

theorem small_linear_nonpos {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D q : ℝ}
    (hD : 0 ≤ D) (hDd : D ≤ d s) (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    D * G p m a z b s q - K p z b s q ≤ 0 := by
  have hlin := sb.linear s q hq0 hq
  by_cases he : 0 ≤ G p m a z b s q
  · have ht := mul_le_mul_of_nonneg_right hDd he
    linarith [hlin.2.2]
  · have ht := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_ge he)
    linarith [hlin.2.1]

theorem centered_affine (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D q Z : ℝ) :
    centered p m a z b s D q Z = centered p m a z b s 0 q Z +
      ((m + b s) * q + C p s * psi p q + a * (1 - q) - C p s - (2 / 5) * z) * D := by
  unfold centered
  ring

theorem incoming_pointwise {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s st : Bool) {D q Z : ℝ}
    (hD : 0 ≤ D) (hDc : D ≤ 197 / 500) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hZ : 0 ≤ Z) (positive : Prop) [Decidable positive]
    (hloc : positive → d st < Z) :
    centered p m a z b s D q Z + (if positive then max (H h st - D) 0 else 0) ≤ 0 := by
  have hgap := centering_gap_nonneg sb.p_nonneg sb.p_le_half hq s
  have hgapZ := mul_nonneg hgap hZ
  have hbq := mul_le_mul_of_nonneg_left hq (sb.b_nonneg s)
  have hbase : centered p m a z b s 0 q Z ≤ -(1 / 4) := by
    have ht := sb.type_one s
    unfold centered
    nlinarith only [hgapZ, hbq, ht]
  have hcap : centered p m a z b s (197 / 500) q Z ≤ 0 := by
    refine (centered_le_linear sb.p_nonneg sb.p_le_half (by norm_num) hq0 hq hZ).trans ?_
    apply small_linear_nonpos sb s (by norm_num) _ hq0 hq
    exact le_trans (by norm_num) (d_lower s)
  have hH := H_bounds sb st
  by_cases hpos : positive
  · simp only [hpos, ↓reduceIte]
    have hzero : centered p m a z b s 0 q Z + H h st ≤ 0 := by
      cases st
      · have ht := sb.type_zero s q hq0 hq
        have hdist : (13 / 25 : ℝ) ≤ Z := (hloc hpos).le
        have hz := mul_le_mul_of_nonneg_left hdist hgap
        change centered p m a z b s 0 q Z + h ≤ 0
        unfold centered
        nlinarith only [ht, hz]
      · change centered p m a z b s 0 q Z + 1 / 4 ≤ 0
        linarith
    rw [centered_affine] at hcap ⊢
    convert affine_hinge_nonpos (by norm_num : (0 : ℝ) < 197 / 500)
      hD hDc hH.1 hH.2 (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hzero) hcap using 1
    ring
  · simp only [hpos, ↓reduceIte, add_zero]
    rw [centered_affine] at hcap ⊢
    have he := affine_hinge_nonpos (by norm_num : (0 : ℝ) < 197 / 500)
      hD hDc hH.1 hH.2 (by norm_num : (0 : ℝ) ≤ 0)
      (show centered p m a z b s 0 q Z + 0 * H h st ≤ 0 by linarith) hcap
    simpa only [zero_mul, add_zero] using he

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def uprime (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (D r : ℝ) : ℝ :=
  ((m * D + b s * (D + 1)) * r - ((2 / 5) * D + 8 / 5) * z) / (C p s * r)

theorem uprime_mul {p m z : ℝ} {b : Bool → ℝ} {s : Bool} {D r : ℝ}
    (hC : 0 < C p s) (hr : 0 < r) :
    uprime p m z b s D r * (C p s * r) =
      (m * D + b s * (D + 1)) * r - ((2 / 5) * D + 8 / 5) * z := by
  exact div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hC) (ne_of_gt hr))

theorem uprime_decompose {p m z : ℝ} {b : Bool → ℝ} {s : Bool} {D r : ℝ}
    (hC : 0 < C p s) (hr : 0 < r) :
    uprime p m z b s D r =
      (D + 1) / C p s * (m + b s - (2 / 5) * z / r) -
        m / C p s - (6 / 5) * z / (C p s * r) := by
  unfold uprime
  field_simp
  nlinarith [hC, hr]

theorem uprime_first {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r ≤ 1) :
    uprime p m z b s D r ≤ (D + 1) * (1 - p) / (1 - p * r) := by
  have hC := C_pos sb.p_le_half s
  have hden := denominator_pos sb.p_le_half sb.p_nonneg hr1
  have h₁ := mul_le_mul_of_nonneg_left (sb.first s r hr hr1)
    (div_nonneg (by linarith : 0 ≤ D + 1) hC.le)
  have h₂ := div_nonneg sb.m_nonneg hC.le
  have h₃ := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) sb.z_nonneg)
    (mul_pos hC hr).le
  have hid : (D + 1) / C p s * (C p s * (1 - p) / (1 - p * r)) =
      (D + 1) * (1 - p) / (1 - p * r) := by
    field_simp
  rw [uprime_decompose hC hr]
  rw [hid] at h₁
  linarith

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem row_le_uprime {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hq : ∀ t, q t ≤ 1)
    (hC : 0 < C p s) (hr : 0 < average π q) :
    rowValue π Z q p m a z b s D R ≤ C p s *
      ((1 - average π q) * R + average π q * uprime p m z b s D (average π q) -
        (D + 1)) := by
  have he := uprime_mul (m := m) (z := z) (b := b) (D := D) hC hr
  have hnonneg := average_nonneg hπ0
    (fun t => mul_nonneg (sub_nonneg.mpr (hq t)) (le_max_right (Z t - a * D) 0))
  unfold rowValue
  nlinarith only [he, hnonneg]

theorem positive_uprime_le_radius {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z h : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1)
    (hD : 0 ≤ D) (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hr : 0 < average π q) (hF : 0 < rowValue π Z q p m a z b s D R) :
    uprime p m z b s D (average π q) ≤ R * (1 - p) := by
  have hr1 := (average_unit_bounds hπ0 hπ hq0 hq).2
  have hden := denominator_pos sb.p_le_half sb.p_nonneg hr1
  have hC := C_pos sb.p_le_half s
  have hrow := row_le_uprime (Z := Z) hπ0 hq hC hr (m := m) (a := a) (z := z) (b := b) (D := D) (R := R)
  have hpos : 0 < (1 - average π q) * R +
      average π q * uprime p m z b s D (average π q) - (D + 1) := by
    by_contra! hn
    have ht := mul_nonpos_of_nonneg_of_nonpos hC.le hn
    linarith
  have hu := uprime_first sb s hD hr hr1
  have hu' := (le_div_iff₀ hden).mp hu
  have hR : (D + 1) / (1 - p * average π q) < R := by
    by_contra! hn
    have hn' := (le_div_iff₀ hden).mp hn
    have ht₁ := mul_le_mul_of_nonneg_left hn' (sub_nonneg.mpr hr1)
    have ht₂ := mul_le_mul_of_nonneg_left hu' hr.le
    have ht₃ := mul_pos hpos hden
    nlinarith only [ht₁, ht₂, ht₃]
  have ht := mul_le_mul_of_nonneg_right hR.le
    (show 0 ≤ 1 - p by linarith [sb.p_le_half])
  exact hu.trans (by simpa only [div_mul_eq_mul_div] using ht)

theorem row_le_excess {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hC : 0 < C p s) (hr : 0 < average π q)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t)
    (hu : uprime p m z b s D (average π q) ≤ R * (1 - p)) :
    rowValue π Z q p m a z b s D R ≤ C p s *
      average π (fun t => max (uprime p m z b s D (average π q) - D - Z t) 0) := by
  have hpoint : ∀ t, (1 - q t) * R + q t * uprime p m z b s D (average π q) -
      D - Z t ≤ max (uprime p m z b s D (average π q) - D - Z t) 0 := by
    intro t
    by_cases hqt : q t < 1
    · have ht₁ := mul_le_mul_of_nonneg_left hu (hq0 t)
      have ht₂ := hcomp t hqt
      have ht₃ := le_max_right (uprime p m z b s D (average π q) - D - Z t) 0
      nlinarith only [ht₁, ht₂, ht₃]
    · have he : q t = 1 := le_antisymm (hq t) (le_of_not_gt hqt)
      simpa only [he, sub_self, zero_mul, one_mul, zero_add] using
        le_max_left (uprime p m z b s D (average π q) - D - Z t) 0
  refine (row_le_uprime hπ0 hq hC hr).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  have ht := average_mono hπ0 hpoint
  simpa only [average_add, average_sub, average_mul_right, average_const hπ, hZ,
    sub_sub] using ht

theorem uprime_charge_bound {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hG : 0 < G p m a z b s r)
    (hKG : K p z b s r ≤ D * G p m a z b s r) :
    uprime p m z b s D r - D ≤ H h s := by
  let T := (C p s * H h s - b s) * r + (8 / 5) * z
  have hcharge : 0 ≤ T * G p m a z b s r + K p z b s r * L p m z b s r := by
    convert sb.charge s r hr.le hr1 using 1
    unfold T G K M L
    ring
  have hL := (sb.linear s r hr.le hr1).1
  have ht := mul_le_mul_of_nonneg_right hKG hL
  have hTG : 0 ≤ (T + L p m z b s r * D) * G p m a z b s r := by
    nlinarith only [hcharge, ht]
  have hT : 0 ≤ T + L p m z b s r * D := nonneg_of_mul_nonneg_left hTG hG
  have hC := C_pos sb.p_le_half s
  have he := uprime_mul (D := D) (m := m) (z := z) (b := b) hC hr
  have hCr := mul_pos hC hr
  have he' : (uprime p m z b s D r - D - H h s) * (C p s * r) =
      -(T + L p m z b s r * D) := by
    unfold T L
    nlinarith only [he]
  have hnonpos : (uprime p m z b s D r - D - H h s) * (C p s * r) ≤ 0 := by
    rw [he']
    exact neg_nonpos.mpr hT
  have := nonpos_of_mul_nonpos_left hnonpos hCr
  linarith

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem finite_charge {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → Bool} {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)) ≤ 0 := by
  classical
  let F : I → ℝ := fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)
  let Γ : I → I → ℝ := fun i t => if 0 < F i then max (H h (s i) - D t) 0 else 0
  have hloc : ∀ i, 0 < F i →
      0 < average π (q i) ∧ 0 < G p m a z b (s i) (average π (q i)) ∧ d (s i) < D i := by
    intro i hi
    exact positive_row_location sb hπ0 hπ hD (hD0 i) hD0 (hq0 i) (hq i) (hcomp i) hi
  have hout : ∀ i, 0 < F i → F i ≤ average π (Γ i) := by
    intro i hi
    have hli := hloc i hi
    have hr1 := (average_unit_bounds hπ0 hπ (hq0 i) (hq i)).2
    have hlin := row_le_linear (m := m) (a := a) (z := z) (b := b) (s := s i)
      hπ0 hπ hD sb.p_nonneg sb.p_le_half (hD0 i) hD0 (hq0 i) (hq i) (hcomp i)
    have hKG : K p z b (s i) (average π (q i)) ≤
        D i * G p m a z b (s i) (average π (q i)) := by
      change 0 < rowValue π D (q i) p m a z b (s i) (D i) (R i) at hi
      linarith
    have hheight := uprime_charge_bound sb (s i) hli.1 hr1 hli.2.1 hKG
    have hu := positive_uprime_le_radius sb hπ0 hπ (hD0 i) (hq0 i) (hq i) hli.1 hi
    have hexcess := row_le_excess hπ0 hπ hD (C_pos sb.p_le_half (s i)) hli.1
      (hq0 i) (hq i) (hcomp i) hu (a := a)
    have hpoint : ∀ t, max (uprime p m z b (s i) (D i) (average π (q i)) - D i - D t) 0 ≤
        max (H h (s i) - D t) 0 := by
      intro t
      exact max_le_max_right 0 (sub_le_sub_right hheight (D t))
    have h₁ := mul_le_mul_of_nonneg_left (average_mono hπ0 hpoint) (C_pos sb.p_le_half (s i)).le
    have hnonneg := average_nonneg hπ0 (fun t => le_max_right (H h (s i) - D t) 0)
    have h₂ := mul_le_mul_of_nonneg_right (C_le_one sb.p_nonneg (s i)) hnonneg
    change F i ≤ average π (fun t => if 0 < F i then max (H h (s i) - D t) 0 else 0)
    simp only [hi, ↓reduceIte]
    exact hexcess.trans (h₁.trans (by simpa only [one_mul] using h₂))
  have hin : ∀ i, D i ≤ 197 / 500 → F i + average π (fun t => Γ t i) ≤ 0 := by
    intro i hi
    have hrow := row_le_centered (m := m) (a := a) (z := z) (b := b) (s := s i)
      hπ0 hπ hD sb.p_nonneg sb.p_le_half (hq i) (hcomp i)
    have hpoint : ∀ t, centered p m a z b (s i) (D i) (q i t) (D t) + Γ t i ≤ 0 := by
      intro t
      exact incoming_pointwise sb (s i) (s t) (hD0 i) hi (hq0 i t) (hq i t) (hD0 t)
        (0 < F t) (fun ht => (hloc t ht).2.2)
    have hav := average_mono hπ0 hpoint
    rw [average_add, average_const hπ] at hav
    change F i ≤ _ at hrow
    linarith
  have hΓ : ∀ i t, 0 ≤ Γ i t := by
    intro i t
    dsimp only [Γ]
    split_ifs <;> positivity
  have hsupport : ∀ i t, ¬ D t ≤ 197 / 500 → Γ i t = 0 := by
    intro i t ht
    have hH := (H_bounds sb (s i)).2
    have he : H h (s i) - D t ≤ 0 := by linarith
    dsimp only [Γ]
    split_ifs
    · exact max_eq_right he
    · rfl
  exact charge_cancellation π F Γ (fun i => D i ≤ 197 / 500) hπ0 hΓ hout hin hsupport

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def rawRow {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : ℝ :=
  (1 - p * s) * (1 - average π q) * R +
    average π q * (m * D + (2 - s) * p * y * (D + 1)) -
    (1 - p * s) * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0)

theorem rawRow_affine {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : rawRow π Z q p m y s D R =
      (1 - s) * rawRow π Z q p m y 0 D R + s * rawRow π Z q p m y 1 D R := by
  unfold rawRow
  ring

theorem affine_le_max {u v s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * u + s * v ≤ max u v := by
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left u v) (sub_nonneg.mpr hs1)
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right u v) hs0
  nlinarith only [h₁, h₂]

theorem rawRow_mono_y {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m y y' s D R : ℝ} (hπ0 : ∀ t, 0 ≤ π t) (hp : 0 ≤ p)
    (hD : 0 ≤ D) (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hs : s ≤ 1) (hy : y ≤ y') : rawRow π Z q p m y s D R ≤ rawRow π Z q p m y' s D R := by
  have hr := average_nonneg hπ0 hq0
  have hlin := mul_le_mul_of_nonneg_left hy
    (mul_nonneg (mul_nonneg (mul_nonneg hr (by linarith : 0 ≤ 2 - s)) hp)
      (by linarith : 0 ≤ D + 1))
  have hhinge : average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y') * D) 0) ≤
      average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0) := by
    apply average_mono hπ0
    intro t
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hq t))
    apply max_le_max_right
    have ht := mul_le_mul_of_nonneg_left hy (mul_nonneg (by positivity : 0 ≤ 2 * p) hD)
    nlinarith only [ht]
  unfold rawRow
  nlinarith only [hlin, hhinge]

noncomputable def endpoint (s : Bool) : ℝ := if s then 1 else 0

theorem rawRow_eq_rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y z D R : ℝ) (s : Bool) :
    rawRow π Z q p m y (endpoint s) D R =
      rowValue π Z q p m (1 + m + 2 * p * y) z
        (fun s => (2 - endpoint s) * p * y) s D R + ((2 / 5) * D + 8 / 5) * z := by
  cases s <;> simp only [rawRow, rowValue, C, endpoint, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem finite_raw_of_scalar {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {p m y z h : ℝ}
    (sb : ScalarBounds p m (1 + m + 2 * p * y) z h (fun s => (2 - endpoint s) * p * y))
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rawRow π D (q i) p m y (s i) (D i) (R i)) ≤ 2 * z := by
  classical
  let v : I → Bool := fun i => decide
    (rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i))
  have hpoint : ∀ i, rawRow π D (q i) p m y (s i) (D i) (R i) ≤
      rawRow π D (q i) p m y (endpoint (v i)) (D i) (R i) := by
    intro i
    rw [rawRow_affine]
    have he := affine_le_max (u := rawRow π D (q i) p m y 0 (D i) (R i))
      (v := rawRow π D (q i) p m y 1 (D i) (R i)) (hs0 i) (hs i)
    by_cases hle : rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i)
    · simpa only [v, hle, decide_true, endpoint, ↓reduceIte, max_eq_right hle] using he
    · simpa only [v, hle, decide_false, endpoint, Bool.false_eq_true, ↓reduceIte,
        max_eq_left (le_of_not_ge hle)] using he
  have hcharge := finite_charge (s := v) sb hπ0 hπ hD0 hD hq0 hq hcomp
  have hav := average_mono hπ0 hpoint
  simp only [rawRow_eq_rowValue (z := z), average_add, average_mul_right,
    average_mul, average_const hπ, hD] at hav
  linarith

end MetricKMedian.FiniteComparison


end
end

end OAI
