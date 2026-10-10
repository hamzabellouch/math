import OAI.Analysis.HenonEmden.CapGeometry

namespace OAI

universe uT

section CapWeights

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {T : Type uT} [MetricSpace T]

/-- A Lipschitz tent profile suffices for the pressure argument; no derivative
of the profile is used in the layer or interval integration. -/
def profile (θ : T) (l : ℝ) (e : T) : ℝ := max (1-dist e θ/l) 0

lemma profile_nonneg (θ : T) (l : ℝ) (e : T) : 0 ≤ profile θ l e := le_max_right _ _
lemma profile_le_one (θ : T) {l : ℝ} (hl : 0 < l) (e : T) : profile θ l e ≤ 1 := by
  unfold profile
  apply max_le _ (by norm_num)
  linarith [div_nonneg (dist_nonneg (x := e) (y := θ)) hl.le]
lemma profile_eq_zero {θ e : T} {l : ℝ} (hl : 0 < l) (he : e ∉ ball θ l) :
    profile θ l e = 0 := by
  unfold profile
  apply max_eq_right
  have hh : l ≤ dist e θ := not_lt.mp he
  have hr : 1 ≤ dist e θ/l := (le_div_iff₀ hl).mpr (by simpa using hh)
  linarith
lemma profile_half {θ e : T} {l : ℝ} (hl : 0 < l) (he : e ∈ ball θ (l/2)) :
    1/2 ≤ profile θ l e := by
  apply le_trans _ (le_max_left _ _)
  have hh : dist e θ/l < 1/2 := (div_lt_iff₀ hl).mpr (by simpa [div_eq_mul_inv,mul_comm] using he)
  linarith
lemma continuous_profile (θ : T) (l : ℝ) : Continuous (profile θ l) := by
  unfold profile
  fun_prop

lemma profile_as_div (θ : T) {l : ℝ} (hl : 0 < l) (e : T) :
    profile θ l e = max (l-dist e θ) 0/l := by
  unfold profile
  rw [← max_div_div_right hl.le,zero_div]
  congr 1
  field_simp [ne_of_gt hl]

lemma profile_center_oscillation {θ θ' e : T} {l : ℝ} (hl : 0 < l) :
    |profile θ l e-profile θ' l e| ≤ dist θ θ'/l := by
  unfold profile
  calc
    _ ≤ |(1-dist e θ/l)-(1-dist e θ'/l)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist e θ-dist e θ'|/l := by
      rw [show (1-dist e θ/l)-(1-dist e θ'/l) = -(dist e θ-dist e θ')/l by ring,
        abs_div,abs_neg,abs_of_pos hl]
    _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [dist_comm e] using abs_dist_sub_le θ θ' e) hl.le

lemma profile_radial_oscillation {θ e : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') :
    |profile θ l e-profile θ l' e| ≤ 2*|l-l'|/l := by
  let a := max (l-dist e θ) 0
  let b := max (l'-dist e θ) 0
  have hab : |a-b| ≤ |l-l'| := by
    simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (l-dist e θ) (l'-dist e θ) 0
  have heq : profile θ l e-profile θ l' e = (a-b)/l+(l'-l)/l*profile θ l' e := by
    rw [profile_as_div _ hl,profile_as_div _ hl']
    dsimp [a,b]
    field_simp [ne_of_gt hl,ne_of_gt hl']
    ring
  rw [heq]
  calc
    _ ≤ |(a-b)/l|+|(l'-l)/l*profile θ l' e| := abs_add_le _ _
    _ = |a-b|/l+|l-l'|/l*profile θ l' e := by
      rw [abs_mul,abs_div,abs_div,abs_of_pos hl,abs_sub_comm l',
        abs_of_nonneg (profile_nonneg _ _ _)]
    _ ≤ |l-l'|/l+|l-l'|/l*1 := by
      gcongr
      exact profile_le_one _ hl' _
    _ = _ := by ring

lemma profile_oscillation {θ θ' e : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') :
    |profile θ l e-profile θ' l' e| ≤ (dist θ θ'+2*|l-l'|)/l := by
  calc
    _ ≤ |profile θ l e-profile θ' l e|+|profile θ' l e-profile θ' l' e| := abs_sub_le _ _ _
    _ ≤ dist θ θ'/l+2*|l-l'|/l := add_le_add (profile_center_oscillation hl) (profile_radial_oscillation hl hl')
    _ = _ := by ring

variable [MeasurableSpace T] [BorelSpace T] (σ : Measure T) [IsFiniteMeasure σ] [CompactSpace T]

def normalizer (θ : T) (l : ℝ) : ℝ := ∫ e, profile θ l e ∂σ

lemma integrable_profile (θ : T) (l : ℝ) : Integrable (profile θ l) σ := by
  have hh := (continuous_profile θ l).continuousOn.integrableOn_compact (μ := σ) isCompact_univ
  simpa only [integrableOn_univ] using hh

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalizer_nonneg (θ : T) (l : ℝ) : 0 ≤ normalizer σ θ l :=
  integral_nonneg (profile_nonneg θ l)

lemma normalizer_bounds (θ : T) {l : ℝ} (hl : 0 < l) :
    (σ (ball θ (l/2))).toReal/2 ≤ normalizer σ θ l ∧
    normalizer σ θ l ≤ (σ (ball θ l)).toReal := by
  have hlo (e : T) : (ball θ (l/2)).indicator (fun _ => (1/2:ℝ)) e ≤ profile θ l e := by
    by_cases he : e ∈ ball θ (l/2)
    · rw [indicator_of_mem he]; exact profile_half hl he
    · rw [indicator_of_notMem he]; exact profile_nonneg _ _ _
  have hhi (e : T) : profile θ l e ≤ (ball θ l).indicator (fun _ => (1:ℝ)) e := by
    by_cases he : e ∈ ball θ l
    · rw [indicator_of_mem he]; exact profile_le_one _ hl _
    · rw [indicator_of_notMem he,profile_eq_zero hl he]
  constructor
  · have hh := integral_mono ((integrable_const (1/2:ℝ)).indicator measurableSet_ball)
      (integrable_profile σ θ l) hlo
    simpa only [integral_indicator measurableSet_ball,integral_const,Measure.real,Measure.restrict_apply_univ,
      smul_eq_mul,one_mul,div_eq_mul_inv,normalizer] using hh
  · have hh := integral_mono (integrable_profile σ θ l)
      ((integrable_const (1:ℝ)).indicator measurableSet_ball) hhi
    simpa only [integral_indicator measurableSet_ball,integral_const,Measure.real,Measure.restrict_apply_univ,
      smul_eq_mul,one_mul,mul_one,normalizer] using hh

lemma continuousOn_normalizer : ContinuousOn (fun z : T × ℝ => normalizer σ z.1 z.2)
    {z | 0 < z.2} := by
  apply continuousOn_integral_of_compact_support (μ := σ) isCompact_univ
  · change ContinuousOn (fun z : (T × ℝ) × T => max (1-dist z.2 z.1.1/z.1.2) 0)
      ({z : T × ℝ | 0 < z.2} ×ˢ univ)
    apply ContinuousOn.sup _ continuousOn_const
    apply continuousOn_const.sub
    apply ContinuousOn.div
    · exact (continuous_snd.dist continuous_fst.fst).continuousOn
    · exact continuous_fst.snd.continuousOn
    · intro z hz; exact ne_of_gt hz.1
  · intro p x hp hx
    exact (hx (mem_univ x)).elim

/-- Every cap is normalized exactly, with no rotational-invariance assumption. -/
def normalized (θ : T) (l : ℝ) (e : T) : ℝ := profile θ l e / normalizer σ θ l

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma integral_normalized {θ : T} {l : ℝ} (hZ : normalizer σ θ l ≠ 0) :
    (∫ e, normalized σ θ l e ∂σ) = 1 := by
  unfold normalized
  rw [integral_div,← normalizer,div_self hZ]

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalized_nonneg (θ : T) (l : ℝ) (e : T) : 0 ≤ normalized σ θ l e :=
  div_nonneg (profile_nonneg _ _ _) (normalizer_nonneg σ _ _)

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalized_le_inv (θ : T) {l : ℝ} (hl : 0 < l) (e : T) :
    normalized σ θ l e ≤ (normalizer σ θ l)⁻¹ := by
  simpa only [one_div,normalized] using div_le_div_of_nonneg_right (profile_le_one θ hl e)
    (normalizer_nonneg σ θ l)

lemma normalizer_oscillation {θ θ' : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l')
    {Q : ℝ} (hQ : (dist θ θ'+2*|l-l'|)/l ≤ Q) :
    |normalizer σ θ l-normalizer σ θ' l'| ≤
      Q*((σ (ball θ l)).toReal+(σ (ball θ' l')).toReal) := by
  have hQ0 : 0 ≤ Q := (div_nonneg (by positivity) hl.le).trans hQ
  let F := (ball θ l).indicator (fun _ => Q)
  let G := (ball θ' l').indicator (fun _ => Q)
  have hF : Integrable F σ := (integrable_const Q).indicator measurableSet_ball
  have hG : Integrable G σ := (integrable_const Q).indicator measurableSet_ball
  have hpt (e : T) : |profile θ l e-profile θ' l' e| ≤ F e+G e := by
    have hh := (profile_oscillation (θ := θ) (θ' := θ') (e := e) hl hl').trans hQ
    by_cases he : e ∈ ball θ l <;> by_cases he' : e ∈ ball θ' l'
    · simp only [F,G,indicator_of_mem he,indicator_of_mem he']; linarith
    · simpa only [F,G,indicator_of_mem he,indicator_of_notMem he',add_zero] using hh
    · simpa only [F,G,indicator_of_notMem he,indicator_of_mem he',zero_add] using hh
    · simp only [F,G,indicator_of_notMem he,indicator_of_notMem he',
        profile_eq_zero hl he,profile_eq_zero hl' he',sub_self,abs_zero,add_zero,le_refl]
  calc
    _ = |∫ e, profile θ l e-profile θ' l' e ∂σ| := by
      rw [integral_sub (integrable_profile σ _ _) (integrable_profile σ _ _)]; rfl
    _ ≤ ∫ e, |profile θ l e-profile θ' l' e| ∂σ := abs_integral_le_integral_abs
    _ ≤ ∫ e, F e+G e ∂σ := integral_mono
      ((integrable_profile σ _ _).sub (integrable_profile σ _ _)).abs (hF.add hG) hpt
    _ = _ := by
      rw [integral_add hF hG]
      simp only [F,G,integral_indicator measurableSet_ball,integral_const,Measure.real,
        Measure.restrict_apply_univ,smul_eq_mul]
      ring

lemma normalized_oscillation {θ θ' : T} {l l' L U Q : ℝ}
    (hl : 0 < l) (hl' : 0 < l') (hL : 0 < L)
    (hZ : L ≤ normalizer σ θ l) (hZ' : L ≤ normalizer σ θ' l')
    (hU : (σ (ball θ l)).toReal+(σ (ball θ' l')).toReal ≤ U)
    (hQ : (dist θ θ'+2*|l-l'|)/l ≤ Q) (e : T) :
    |normalized σ θ l e-normalized σ θ' l' e| ≤ (1/L+U/L^2)*Q := by
  have hQ0 : 0 ≤ Q := (div_nonneg (by positivity) hl.le).trans hQ
  have hU0 : 0 ≤ U := (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg).trans hU
  have hp := (profile_oscillation (θ := θ) (θ' := θ') (e := e) hl hl').trans hQ
  have hz := (normalizer_oscillation σ hl hl' hQ).trans (mul_le_mul_of_nonneg_left hU hQ0)
  have hz0 : 0 < normalizer σ θ l := hL.trans_le hZ
  have hz0' : 0 < normalizer σ θ' l' := hL.trans_le hZ'
  have he : normalized σ θ l e-normalized σ θ' l' e =
      (profile θ l e-profile θ' l' e)/normalizer σ θ l +
      profile θ' l' e*(normalizer σ θ' l'-normalizer σ θ l)/
        (normalizer σ θ l*normalizer σ θ' l') := by
    unfold normalized
    field_simp [ne_of_gt hz0,ne_of_gt hz0']
    ring
  rw [he]
  calc
    _ ≤ |(profile θ l e-profile θ' l' e)/normalizer σ θ l|+
        |profile θ' l' e*(normalizer σ θ' l'-normalizer σ θ l)/(normalizer σ θ l*normalizer σ θ' l')| := abs_add_le _ _
    _ = |profile θ l e-profile θ' l' e|/normalizer σ θ l+
        profile θ' l' e*|normalizer σ θ l-normalizer σ θ' l'|/
          (normalizer σ θ l*normalizer σ θ' l') := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hz0,abs_of_pos (mul_pos hz0 hz0'),
        abs_of_nonneg (profile_nonneg _ _ _),abs_sub_comm (normalizer σ θ' l')]
    _ ≤ Q/L+1*(Q*U)/(L*L) := by
      gcongr
      exact profile_le_one _ hl' _
    _ = _ := by ring

end HenonLaneEmden.CapWeights
end
end CapWeights

end OAI
