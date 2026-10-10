import Mathlib

namespace OAI

/-! Fourier extension from the unit sphere in the fourth-power range. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace EllipticCapacity

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := {ω : Space // ω ∈ Metric.sphere (0 : Space) 1}

def surfaceArea : Measure Sphere := (volume : Measure Space).toSphere

def extension (g : Sphere → ℂ) (x : Space) : ℂ :=
  ∫ ω, g ω * Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ)) ∂surfaceArea

def SphereRestriction : Prop :=
  ∀ p : ℝ, 3 < p → ∃ C : ℝ≥0, ∀ g : Sphere → ℂ,
    Measurable g → (∃ M : ℝ, ∀ ω, ‖g ω‖ ≤ M) →
    eLpNorm (extension g) (ENNReal.ofReal p) volume ≤
      (C : ℝ≥0∞) * eLpNorm g ∞ surfaceArea

theorem surfaceArea_univ : surfaceArea Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  unfold surfaceArea
  rw [Measure.toSphere_apply_univ]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin,
    EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_natCast]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

theorem kernel_norm (x : Space) (ω : Sphere) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ x (ω : Space) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

instance surfaceArea_isFiniteMeasure : IsFiniteMeasure surfaceArea := by
  constructor
  rw [surfaceArea_univ]
  exact ENNReal.ofReal_lt_top

theorem extension_integrable {g : Sphere → ℂ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ ω, ‖g ω‖ ≤ M) (x : Space) :
    Integrable (fun ω => g ω * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ))) surfaceArea := by
  have hm : Measurable (fun ω : Sphere => g ω * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ))) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable M
  filter_upwards [] with ω
  simpa only [norm_mul, kernel_norm, mul_one] using hM ω

theorem extension_norm_le {g : Sphere → ℂ} {M : ℝ}
    (hM : ∀ ω, ‖g ω‖ ≤ M) (x : Space) : ‖extension g x‖ ≤ M * (4 * Real.pi) := by
  unfold extension
  have hmass : surfaceArea.real Set.univ = 4 * Real.pi := by
    rw [Measure.real, surfaceArea_univ, ENNReal.toReal_ofReal]
    positivity
  rw [← hmass]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with ω
  simpa only [norm_mul, kernel_norm, mul_one] using hM ω

theorem extension_continuous {g : Sphere → ℂ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ ω, ‖g ω‖ ≤ M) : Continuous (extension g) := by
  apply continuous_of_dominated
    (bound := fun _ : Sphere => M)
    (fun x => (extension_integrable hg hM x).aestronglyMeasurable)
  · intro x
    filter_upwards [] with ω
    simpa only [norm_mul, kernel_norm, mul_one] using hM ω
  · exact integrable_const M
  · filter_upwards [] with ω
    fun_prop

theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) -
      Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := by
    intro x
    simpa using (((hasDerivAt_id (x : ℂ)).comp_ofReal).mul_const Complex.I).cexp
  have hb : ∀ x : ℝ, ‖Complex.exp ((x : ℂ) * Complex.I) * Complex.I‖ ≤ 1 := by
    intro x
    simp [Complex.norm_exp]
  simpa using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => (hd x).hasDerivWithinAt)
    (fun x _ => hb x) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ b) (Set.mem_univ a)

theorem kernel_norm_sub_le (x y : Space) (ω : Sphere) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ)) -
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y (ω : Space) : ℂ))‖ ≤
      2 * Real.pi * ‖x - y‖ := by
  have h := norm_exp_mul_I_sub_le (2 * Real.pi * inner ℝ x (ω : Space))
    (2 * Real.pi * inner ℝ y (ω : Space))
  have hω : ‖(ω : Space)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hi : |inner ℝ (x - y) (ω : Space)| ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs, hω, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (x - y) (ω : Space)
  have he : ∀ a : ℝ, (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I := by
    intro a
    push_cast
    ring
  simp only [he] at ⊢
  refine h.trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
    ← inner_sub_left]
  exact mul_le_mul_of_nonneg_left hi (by positivity)

theorem extension_norm_sub_le {g : Sphere → ℂ} (hg : Measurable g)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, ‖g ω‖ ≤ M) (x y : Space) :
    ‖extension g x - extension g y‖ ≤
      (8 * Real.pi ^ 2 * M) * ‖x - y‖ := by
  unfold extension
  rw [← integral_sub (extension_integrable hg hM x) (extension_integrable hg hM y)]
  have hmass : surfaceArea.real Set.univ = 4 * Real.pi := by
    rw [Measure.real, surfaceArea_univ, ENNReal.toReal_ofReal]
    positivity
  have hbound := norm_integral_le_of_norm_le_const (μ := surfaceArea)
    (C := M * (2 * Real.pi * ‖x - y‖)) (f := fun ω : Sphere =>
      g ω * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ)) -
      g ω * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y (ω : Space) : ℂ)))
    (by
      filter_upwards [] with ω
      rw [← mul_sub, norm_mul]
      exact mul_le_mul (hM ω) (kernel_norm_sub_le x y ω) (norm_nonneg _) hM0)
  rw [hmass] at hbound
  convert hbound using 1
  ring

open Filter

def SphereFourthPower : Prop :=
  ∀ g : Sphere → ℂ, Measurable g → (∃ M : ℝ, ∀ ω, ‖g ω‖ ≤ M) →
    (eLpNorm (extension g) 4 volume) ^ 4 ≤
      ENNReal.ofReal (32 * Real.pi ^ 3) * (eLpNorm g ∞ surfaceArea) ^ 4

def character (x v : Space) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x v : ℂ))

lemma character_norm (x v : Space) : ‖character x v‖ = 1 := by
  simp [character, Complex.norm_exp]
lemma character_add (x v w : Space) : character x (v + w) = character x v * character x w := by
  simp [character, inner_add_right, mul_add, Complex.exp_add]
lemma character_neg (x v : Space) : character x (-v) = star (character x v) := by
  simp [character, inner_neg_right, ← Complex.exp_conj]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by change star (2 : ℂ) = _; simp]

abbrev Quad := (Sphere × Sphere) × (Sphere × Sphere)
def quadMeasure : Measure Quad := (surfaceArea.prod surfaceArea).prod (surfaceArea.prod surfaceArea)
instance : IsFiniteMeasure quadMeasure := inferInstanceAs (IsFiniteMeasure ((surfaceArea.prod surfaceArea).prod (surfaceArea.prod surfaceArea)))
def quadVector (q : Quad) : Space := (q.1.1 : Space) + q.1.2 - ((q.2.1 : Space) + q.2.2)
def quadAmplitude (g : Sphere → ℂ) (q : Quad) : ℂ := g q.1.1 * g q.1.2 * star (g q.2.1 * g q.2.2)

lemma quad_character (x : Space) (q : Quad) :
    character x (quadVector q) = character x q.1.1 * character x q.1.2 *
      star (character x q.2.1 * character x q.2.2) := by
  simp only [quadVector, sub_eq_add_neg, character_add, character_neg, star_mul]

lemma fourth_power_expansion {g : Sphere → ℂ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ ω, ‖g ω‖ ≤ M) (x : Space) :
    (‖extension g x‖ ^ 4 : ℝ) = (∫ q, quadAmplitude g q * character x (quadVector q) ∂quadMeasure : ℂ) := by
  let f : Sphere → ℂ := fun ω => g ω * character x ω
  have hf : Integrable f surfaceArea := extension_integrable hg hM x
  have hc : (∫ q : Sphere × Sphere, star (f q.1 * f q.2) ∂surfaceArea.prod surfaceArea) =
      star (extension g x ^ 2) := by
    change (∫ q : Sphere × Sphere, (starRingEnd ℂ) (f q.1 * f q.2) ∂surfaceArea.prod surfaceArea) = _
    rw [integral_conj, integral_prod_mul]
    simp only [pow_two]
    rfl
  have hp := integral_prod_mul (μ := surfaceArea.prod surfaceArea) (ν := surfaceArea.prod surfaceArea)
    (fun q : Sphere × Sphere => f q.1 * f q.2) (fun q : Sphere × Sphere => star (f q.1 * f q.2))
  have hq : (∫ q, quadAmplitude g q * character x (quadVector q) ∂quadMeasure) =
      extension g x ^ 2 * star (extension g x ^ 2) := by
    calc
      _ = ∫ q : Quad, f q.1.1 * f q.1.2 * star (f q.2.1 * f q.2.2) ∂quadMeasure := by
        apply integral_congr_ae
        filter_upwards [] with q
        simp only [quadAmplitude, quad_character, f, star_mul]
        ring
      _ = _ := by
        rw [quadMeasure, hp, hc, integral_prod_mul]
        simp only [pow_two]
        rfl
  rw [hq]
  change ((‖extension g x‖ ^ 4 : ℝ) : ℂ) =
    extension g x ^ 2 * (starRingEnd ℂ) (extension g x ^ 2)
  rw [RCLike.mul_conj]
  change (↑(‖extension g x‖ ^ 4) : ℂ) = (↑(‖extension g x ^ 2‖) : ℂ) ^ 2
  rw [norm_pow, ← Complex.ofReal_pow, ← pow_mul]

lemma quadAmplitude_bound {g : Sphere → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ω, ‖g ω‖ ≤ M) (q : Quad) : ‖quadAmplitude g q‖ ≤ M ^ 4 := by
  unfold quadAmplitude
  simp only [norm_mul, norm_star]
  calc
    _ ≤ (M * M) * (M * M) := by gcongr <;> apply hM
    _ = _ := by ring

def gaussian (b : ℝ) (x : Space) : ℝ := Real.exp (-b * ‖x‖ ^ 2)
def heatKernel (b : ℝ) (v : Space) : ℝ :=
  (Real.pi / b) ^ (3 / 2 : ℝ) * Real.exp (-Real.pi ^ 2 * ‖v‖ ^ 2 / b)

lemma gaussian_pos (b : ℝ) (x : Space) : 0 < gaussian b x := Real.exp_pos _
lemma heatKernel_nonneg {b : ℝ} (hb : 0 < b) (v : Space) : 0 ≤ heatKernel b v := by
  unfold heatKernel
  positivity

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) : Integrable (gaussian b) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Space)
    (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  change Integrable (fun x : Space => Real.exp (-b * ‖x‖ ^ 2))
  simpa [Complex.norm_exp, neg_mul, ← Complex.ofReal_pow] using h

lemma gaussian_character_integral {b : ℝ} (hb : 0 < b) (v : Space) :
    (∫ x, (gaussian b x : ℂ) * character x v) = (heatKernel b v : ℂ) := by
  have heq : (fun x : Space => (gaussian b x : ℂ) * character x v) =
      (fun x : Space => Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + 2 * Real.pi * Complex.I * (inner ℝ v x : ℂ))) := by
    ext x
    rw [gaussian, character, Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm x v]
    push_cast
    rfl
  rw [heq, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  unfold heatKernel
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le), Complex.ofReal_exp]
  push_cast
  congr 1
  congr 1
  rw [show (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = -4 * (Real.pi : ℂ) ^ 2 by
    ring_nf; simp [Complex.I_sq]]
  ring

lemma gaussian_quad_integrable {b M : ℝ} (hb : 0 < b) (hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    Integrable (fun p : Space × Quad => (gaussian b p.1 : ℂ) *
      (quadAmplitude g p.2 * character p.1 (quadVector p.2))) (volume.prod quadMeasure) := by
  apply ((gaussian_integrable hb).mul_prod (integrable_const (M ^ 4) : Integrable (fun _ : Quad => M ^ 4) quadMeasure)).mono'
  · unfold gaussian quadAmplitude character quadVector
    fun_prop
  · filter_upwards [] with p
    simp only [norm_mul, character_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (gaussian_pos _ _)]
    exact mul_le_mul_of_nonneg_left (quadAmplitude_bound hM0 hM _) (gaussian_pos _ _).le

lemma gaussian_fourth_identity {b M : ℝ} (hb : 0 < b) (hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    ((∫ x, gaussian b x * ‖extension g x‖ ^ 4 : ℝ) : ℂ) =
      ∫ q, quadAmplitude g q * (heatKernel b (quadVector q) : ℂ) ∂quadMeasure := by
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]
  simp_rw [fourth_power_expansion hg hM, ← integral_const_mul]
  rw [integral_integral_swap (gaussian_quad_integrable hb hM0 hg hM)]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [show (fun x : Space => (gaussian b x : ℂ) * (quadAmplitude g q * character x (quadVector q))) =
    (fun x : Space => quadAmplitude g q * ((gaussian b x : ℂ) * character x (quadVector q))) by
      funext x; ring]
  rw [integral_const_mul, gaussian_character_integral hb]

lemma heatKernel_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun q : Quad => heatKernel b (quadVector q)) quadMeasure := by
  apply Integrable.of_bound (C := (Real.pi / b) ^ (3 / 2 : ℝ))
  · unfold heatKernel quadVector
    fun_prop
  · filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hb _)]
    unfold heatKernel
    apply mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hb.le
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

lemma gaussian_fourth_integrable {b M : ℝ} (hb : 0 < b) (_hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    Integrable (fun x => gaussian b x * ‖extension g x‖ ^ 4) := by
  apply (gaussian_integrable hb).mul_bdd (c := (M * (4 * Real.pi)) ^ 4)
    ((extension_continuous hg hM).norm.pow 4).aestronglyMeasurable
  filter_upwards [] with x
  simp only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
  exact pow_le_pow_left₀ (norm_nonneg _) (extension_norm_le hM x) 4

lemma gaussian_fourth_bound {b M : ℝ} (hb : 0 < b) (hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    (∫ x, gaussian b x * ‖extension g x‖ ^ 4) ≤
      M ^ 4 * ∫ x, gaussian b x * ‖extension (fun _ => 1) x‖ ^ 4 := by
  have hn (g : Sphere → ℂ) : 0 ≤ ∫ x, gaussian b x * ‖extension g x‖ ^ 4 :=
    integral_nonneg (fun x => mul_nonneg (gaussian_pos _ _).le (by positivity))
  have h1 := gaussian_fourth_identity (M := 1) hb (by norm_num)
    (g := fun _ => 1) measurable_const (fun _ => by simp)
  have h1' : (∫ x, gaussian b x * ‖extension (fun _ => 1) x‖ ^ 4) =
      ∫ q, heatKernel b (quadVector q) ∂quadMeasure := by
    have : ((∫ x, gaussian b x * ‖extension (fun _ => 1) x‖ ^ 4 : ℝ) : ℂ) =
        ((∫ q, heatKernel b (quadVector q) ∂quadMeasure : ℝ) : ℂ) := by
      simpa [quadAmplitude, integral_complex_ofReal] using h1
    exact_mod_cast this
  rw [h1']
  have hi := gaussian_fourth_identity hb hM0 hg hM
  calc
    _ = ‖((∫ x, gaussian b x * ‖extension g x‖ ^ 4 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn g)]
    _ = ‖∫ q, quadAmplitude g q * (heatKernel b (quadVector q) : ℂ) ∂quadMeasure‖ := by rw [hi]
    _ ≤ ∫ q, ‖quadAmplitude g q * (heatKernel b (quadVector q) : ℂ)‖ ∂quadMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ q, M ^ 4 * heatKernel b (quadVector q) ∂quadMeasure := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall (fun q => norm_nonneg _)
      · exact (heatKernel_integrable hb).const_mul (M ^ 4)
      · filter_upwards [] with q
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hb _)]
        exact mul_le_mul_of_nonneg_right (quadAmplitude_bound hM0 hM _) (heatKernel_nonneg hb _)
    _ = _ := integral_const_mul _ _

lemma gaussian_le_one {b : ℝ} (hb : 0 ≤ b) (x : Space) : gaussian b x ≤ 1 := by
  unfold gaussian
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _))

lemma lintegral_gaussian_fourth_bound {b M : ℝ} (hb : 0 < b) (hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    (∫⁻ x, ENNReal.ofReal (gaussian b x * ‖extension g x‖ ^ 4)) ≤
      ENNReal.ofReal (M ^ 4) * ∫⁻ x, ENNReal.ofReal (‖extension (fun _ => 1) x‖ ^ 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_fourth_integrable hb hM0 hg hM)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (gaussian_pos b x).le (by positivity)))]
  refine (ENNReal.ofReal_le_ofReal (gaussian_fourth_bound hb hM0 hg hM)).trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [ofReal_integral_eq_lintegral_ofReal
    (gaussian_fourth_integrable (M := 1) hb (by norm_num) measurable_const (fun _ => by simp))
    (Filter.Eventually.of_forall (fun x => mul_nonneg (gaussian_pos b x).le (by positivity)))]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left (by positivity) (gaussian_le_one hb.le x)

lemma fourth_power_majorant {M : ℝ} (hM0 : 0 ≤ M)
    {g : Sphere → ℂ} (hg : Measurable g) (hM : ∀ ω, ‖g ω‖ ≤ M) :
    (∫⁻ x, ENNReal.ofReal (‖extension g x‖ ^ 4)) ≤
      ENNReal.ofReal (M ^ 4) * ∫⁻ x, ENNReal.ofReal (‖extension (fun _ => 1) x‖ ^ 4) := by
  let F : ℕ → Space → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (gaussian ((1 / 2 : ℝ) ^ n) x * ‖extension g x‖ ^ 4)
  have hm : ∀ n, Measurable (F n) := by
    intro n
    dsimp [F]
    have hc := extension_continuous hg hM
    unfold gaussian
    fun_prop
  have ht : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop
      (nhds (ENNReal.ofReal (‖extension g x‖ ^ 4))) := by
    intro x
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have he := Real.continuous_exp.continuousAt.tendsto.comp (hp.neg.mul_const (‖x‖ ^ 2))
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (he.mul_const (‖extension g x‖ ^ 4))
    simpa [F, gaussian, Function.comp_def] using h
  have hfat := lintegral_liminf_le (μ := (volume : Measure Space)) (u := Filter.atTop) hm
  simp_rw [(ht _).liminf_eq] at hfat
  apply hfat.trans
  apply Filter.liminf_le_of_frequently_le
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  exact lintegral_gaussian_fourth_bound (by positivity) hM0 hg hM
  all_goals isBoundedDefault

lemma integral_polar_three (f : Space → ℂ) (hf : Integrable f) :
    ∫ y, f y = ∫ r in Set.Ioi (0 : ℝ),
      r ^ 2 • ∫ ω : Sphere, f (r • (ω : Space)) ∂surfaceArea := by
  let h := homeomorphUnitSphereProd Space
  let μ := (volume : Measure Space)
  let g : Sphere × Set.Ioi (0 : ℝ) → ℂ := fun p => f (p.2.val • (p.1 : Space))
  have heq : g ∘ h = f ∘ Subtype.val := by
    funext y
    dsimp [g]
    rw [← homeomorphUnitSphereProd_symm_apply_coe Space]
    simp [h]
  have hc : Integrable (f ∘ Subtype.val) (μ.comap (Subtype.val : ({0}ᶜ : Set Space) → Space)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Space)).compl).1
      hf.integrableOn
  have hg : Integrable g (surfaceArea.prod (Measure.volumeIoiPow 2)) := by
    have hm := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding h) (g := g)
    rw [heq] at hm
    simpa [Space, surfaceArea, μ] using hm.mp hc
  calc
    ∫ y, f y = ∫ y : ({0}ᶜ : Set Space), f y.val ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton (0 : Space)).compl,
        restrict_compl_singleton]
    _ = ∫ p, g p ∂surfaceArea.prod (Measure.volumeIoiPow 2) := by
      have hi := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding h) g
      change ∫ y, (g ∘ h) y ∂μ.comap Subtype.val = _ at hi
      rw [heq] at hi
      simpa [Space, surfaceArea, μ] using hi
    _ = ∫ r : Set.Ioi (0 : ℝ), ∫ ω : Sphere,
        f (r.val • (ω : Space)) ∂surfaceArea ∂Measure.volumeIoiPow 2 :=
      integral_prod_symm g hg
    _ = ∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 • ∫ ω : Sphere, f (r • (ω : Space)) ∂surfaceArea := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ =>
          Real.toNNReal (r ^ 2) • ∫ ω : Sphere, f (r • (ω : Space)) ∂surfaceArea)]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg r)]
      · exact (measurable_subtype_coe.pow_const 2).real_toNNReal

abbrev CrossPlane := EuclideanSpace ℝ (Fin 2)

def sphereSplit : Space ≃ᵐ ℝ × CrossPlane :=
  (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

lemma sphereSplit_measurePreserving : MeasurePreserving sphereSplit := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) := by
    change MeasurePreserving (Prod.map id (WithLp.toLp 2)) _ _
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (Fin 2))
  exact h3.comp (h2.comp h1)

lemma sphereSplit_symm_apply (u : ℝ) (v : CrossPlane) :
    sphereSplit.symm (u, v) = WithLp.toLp 2 (Fin.cons u (WithLp.ofLp v)) := by
  ext i
  fin_cases i <;> rfl

lemma sphereSplit_norm_sq (u : ℝ) (v : CrossPlane) :
    ‖sphereSplit.symm (u, v)‖ ^ 2 = u ^ 2 + ‖v‖ ^ 2 := by
  rw [sphereSplit_symm_apply, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]

def sphereKernel (x y : Space) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x y : ℂ))

def ballFourier (x : Space) (R : ℝ) : ℂ :=
  ∫ y in Metric.ball (0 : Space) R, sphereKernel x y

lemma ballFourier_polar (x : Space) (R : ℝ) (hR : 0 ≤ R) :
    ballFourier x R = ∫ r in (0 : ℝ)..R,
      r ^ 2 • extension (fun _ => 1) (r • x) := by
  have hcont : Continuous (sphereKernel x) := by unfold sphereKernel; fun_prop
  have hint : Integrable ((Metric.ball (0 : Space) R).indicator (sphereKernel x)) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) R)
        hcont.continuousOn).mono_set Metric.ball_subset_closedBall)
  calc
    ballFourier x R = ∫ y, (Metric.ball (0 : Space) R).indicator (sphereKernel x) y := by
      rw [integral_indicator measurableSet_ball]; rfl
    _ = ∫ r in Set.Ioi (0 : ℝ), r ^ 2 • ∫ ω : Sphere,
        (Metric.ball (0 : Space) R).indicator (sphereKernel x)
          (r • (ω : Space)) ∂surfaceArea := integral_polar_three _ hint
    _ = ∫ r in Set.Ioi (0 : ℝ), (Set.Iio R).indicator
        (fun r => r ^ 2 • extension (fun _ => 1) (r • x)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      have hr0 : 0 < r := hr
      have hn (ω : Sphere) : ‖r • (ω : Space)‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le,
          mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      by_cases hrR : r < R
      · rw [Set.indicator_of_mem (show r ∈ Set.Iio R from hrR)]
        congr 1
        unfold extension
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Set.indicator_of_mem (show r • (ω : Space) ∈ Metric.ball (0 : Space) R by
          simpa only [mem_ball_zero_iff, hn] using hrR)]
        simp [sphereKernel, inner_smul_right, real_inner_smul_left]
      · rw [Set.indicator_of_notMem (show r ∉ Set.Iio R from hrR)]
        have he : ∀ ω : Sphere,
            (Metric.ball (0 : Space) R).indicator (sphereKernel x) (r • (ω : Space)) = 0 := by
          intro ω
          apply Set.indicator_of_notMem
          simpa only [mem_ball_zero_iff, hn] using hrR
        simp only [he, integral_zero, smul_zero]
    _ = ∫ r in (0 : ℝ)..R, r ^ 2 • extension (fun _ => 1) (r • x) := by
      rw [setIntegral_indicator measurableSet_Iio, intervalIntegral.integral_of_le hR,
        integral_Ioc_eq_integral_Ioo]
      congr 1

lemma sphereSplit_symm_first (u : ℝ) (v : CrossPlane) :
    (sphereSplit.symm (u, v)) 0 = u := by
  rw [sphereSplit_symm_apply]
  rfl

lemma sphereSplit_ball_slice (R : ℝ) (hR : 0 ≤ R) (u : ℝ) :
    {v : CrossPlane | sphereSplit.symm (u, v) ∈ Metric.ball (0 : Space) R} =
      Metric.ball (0 : CrossPlane) (Real.sqrt (R ^ 2 - u ^ 2)) := by
  ext v
  simp only [Set.mem_ofPred_eq, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg v)]
  have hn := sphereSplit_norm_sq u v
  constructor <;> intro hv
  · nlinarith [norm_nonneg (sphereSplit.symm (u, v))]
  · nlinarith [norm_nonneg (sphereSplit.symm (u, v))]

lemma plane_slice_volume (R u : ℝ) (hR : 0 ≤ R) :
    (volume : Measure CrossPlane).real
        (Metric.ball 0 (Real.sqrt (R ^ 2 - u ^ 2))) =
      (Set.Ioo (-R) R).indicator (fun u => Real.pi * (R ^ 2 - u ^ 2)) u := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal Real.pi_pos.le]
  by_cases hu : u ∈ Set.Ioo (-R) R
  · rw [Set.indicator_of_mem hu, Real.sq_sqrt]
    · ring
    · have := hu.1
      have := hu.2
      nlinarith
  · rw [Set.indicator_of_notMem hu, Real.sqrt_eq_zero_of_nonpos]
    · ring
    · simp only [mem_Ioo, not_and_or, not_lt] at hu
      rcases hu with h | h <;> nlinarith

lemma integral_ball_head (f : ℝ → ℂ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R) :
    ∫ y in Metric.ball (0 : Space) R, f (y 0) =
      ∫ u in (-R)..R, (Real.pi * (R ^ 2 - u ^ 2)) • f u := by
  let g : Space → ℂ := (Metric.ball (0 : Space) R).indicator (fun y => f (y 0))
  have hc : Continuous (fun y : Space => f (y 0)) := by fun_prop
  have hg : Integrable g := (integrable_indicator_iff measurableSet_ball).2
    ((ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) R)
      hc.continuousOn).mono_set Metric.ball_subset_closedBall)
  have hg' : Integrable (g ∘ sphereSplit.symm)
      ((volume : Measure ℝ).prod (volume : Measure CrossPlane)) := by
    have h := (sphereSplit_measurePreserving.symm.integrable_comp_emb
      sphereSplit.symm.measurableEmbedding).2 hg
    simpa only [Measure.volume_eq_prod] using h
  have hinner (u : ℝ) : ∫ v : CrossPlane, g (sphereSplit.symm (u, v)) =
      (Set.Ioo (-R) R).indicator (fun u => Real.pi * (R ^ 2 - u ^ 2)) u • f u := by
    have he : (fun v : CrossPlane => g (sphereSplit.symm (u, v))) =
        (Metric.ball (0 : CrossPlane) (Real.sqrt (R ^ 2 - u ^ 2))).indicator
          (fun _ => f u) := by
      funext v
      have ht : sphereSplit.symm (u, v) ∈ Metric.ball (0 : Space) R ↔
          v ∈ Metric.ball (0 : CrossPlane) (Real.sqrt (R ^ 2 - u ^ 2)) := by
        change v ∈ {v : CrossPlane | sphereSplit.symm (u, v) ∈ Metric.ball (0 : Space) R} ↔ _
        rw [sphereSplit_ball_slice R hR u]
      by_cases hv : v ∈ Metric.ball (0 : CrossPlane) (Real.sqrt (R ^ 2 - u ^ 2))
      · rw [Set.indicator_of_mem hv]
        change (Metric.ball (0 : Space) R).indicator (fun y => f (y 0))
          (sphereSplit.symm (u, v)) = _
        rw [Set.indicator_of_mem (ht.mpr hv), sphereSplit_symm_first]
      · rw [Set.indicator_of_notMem hv]
        exact Set.indicator_of_notMem (fun h => hv (ht.mp h)) _
    rw [he, integral_indicator measurableSet_ball, setIntegral_const,
      plane_slice_volume R u hR]
  calc
    ∫ y in Metric.ball (0 : Space) R, f (y 0) = ∫ y, g y :=
      (integral_indicator measurableSet_ball).symm
    _ = ∫ p : ℝ × CrossPlane, g (sphereSplit.symm p) :=
      (sphereSplit_measurePreserving.symm.integral_comp' g).symm
    _ = ∫ u : ℝ, ∫ v : CrossPlane, g (sphereSplit.symm (u, v)) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod _ hg'
    _ = ∫ u : ℝ, (Set.Ioo (-R) R).indicator
        (fun u => (Real.pi * (R ^ 2 - u ^ 2)) • f u) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hinner]
      by_cases hu : u ∈ Set.Ioo (-R) R <;> simp [Set.indicator, hu]
    _ = ∫ u in (-R)..R, (Real.pi * (R ^ 2 - u ^ 2)) • f u := by
      rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le (by linarith),
        integral_Ioc_eq_integral_Ioo]

lemma hasDerivAt_symmetric_integral (f : ℝ → ℂ) (hf : Continuous f) (R : ℝ) :
    HasDerivAt (fun r => ∫ u in (-r)..r, f u) (f R + f (-R)) R := by
  have hD (r : ℝ) : HasDerivAt (fun r => ∫ u in (0 : ℝ)..r, f u) (f r) r :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he (r : ℝ) : ∫ u in (-r)..r, f u =
      (∫ u in (0 : ℝ)..r, f u) - ∫ u in (0 : ℝ)..(-r), f u := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 (-r)) (hf.intervalIntegrable (-r) r)
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)
  simp_rw [he]
  simpa only [Pi.sub_def, Function.comp_def, id_eq, neg_one_smul, sub_neg_eq_add]
    using (hD R).sub ((hD (-R)).scomp R (hasDerivAt_id R).neg)

lemma hasDerivAt_weighted_slice (f : ℝ → ℂ) (hf : Continuous f) (R : ℝ) :
    HasDerivAt (fun r => ∫ u in (-r)..r, (Real.pi * (r ^ 2 - u ^ 2)) • f u)
      ((2 * Real.pi * R) • ∫ u in (-R)..R, f u) R := by
  have hcont : Continuous (fun u : ℝ => u ^ 2 • f u) := by fun_prop
  have he (r : ℝ) : (∫ u in (-r)..r, (Real.pi * (r ^ 2 - u ^ 2)) • f u) =
      Real.pi • (r ^ 2 • (∫ u in (-r)..r, f u) -
        ∫ u in (-r)..r, u ^ 2 • f u) := by
    simp_rw [mul_smul, sub_smul]
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_smul]
    · exact (hf.intervalIntegrable _ _).smul _
    · exact hcont.intervalIntegrable _ _
  simp_rw [he]
  convert! ((((hasDerivAt_id R).pow 2).smul (hasDerivAt_symmetric_integral f hf R)).sub
    (hasDerivAt_symmetric_integral _ hcont R)).const_smul Real.pi using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, neg_sq,
    smul_add]
  module

lemma ballFourier_hasDerivAt_one (x : Space) :
    HasDerivAt (ballFourier x) (extension (fun _ => 1) x) 1 := by
  have hec : Continuous (extension (fun _ => (1 : ℂ))) :=
    extension_continuous measurable_const (M := 1) (by simp)
  have hc : Continuous (fun r : ℝ => r ^ 2 • extension (fun _ => 1) (r • x)) := by
    fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0 : ℝ) 1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : ballFourier x =ᶠ[nhds (1 : ℝ)]
      (fun R => ∫ r in (0 : ℝ)..R, r ^ 2 • extension (fun _ => 1) (r • x)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with R hR
    exact ballFourier_polar x R hR.le
  simpa using hd.congr_of_eventuallyEq he

lemma ballFourier_isometry (e : Space ≃ₗᵢ[ℝ] Space) (x : Space) (R : ℝ) :
    ballFourier (e x) R = ballFourier x R := by
  let g : Space → ℂ := (Metric.ball (0 : Space) R).indicator (sphereKernel (e x))
  have he : (fun y => g (e y)) =
      (Metric.ball (0 : Space) R).indicator (sphereKernel x) := by
    funext y
    dsimp [g]
    by_cases hy : y ∈ Metric.ball (0 : Space) R
    · have hey : e y ∈ Metric.ball (0 : Space) R := by
        simpa only [mem_ball_zero_iff, e.norm_map] using hy
      rw [Set.indicator_of_mem hey, Set.indicator_of_mem hy]
      simp only [sphereKernel, e.inner_map_map]
    · have hey : e y ∉ Metric.ball (0 : Space) R := by
        simpa only [mem_ball_zero_iff, e.norm_map] using hy
      rw [Set.indicator_of_notMem hey, Set.indicator_of_notMem hy]
  have hm := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding g
  rw [he, integral_indicator measurableSet_ball] at hm
  dsimp only [g] at hm
  rw [integral_indicator measurableSet_ball] at hm
  exact hm.symm

lemma extension_one_isometry (e : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    extension (fun _ => 1) (e x) = extension (fun _ => 1) x := by
  have he : ballFourier (e x) = ballFourier x := funext (ballFourier_isometry e x)
  have h := ballFourier_hasDerivAt_one (e x)
  rw [he] at h
  exact h.unique (ballFourier_hasDerivAt_one x)

def spaceAxis (t : ℝ) : Space := PiLp.single 2 0 t

lemma spaceAxis_norm (t : ℝ) : ‖spaceAxis t‖ = |t| := by
  simp [spaceAxis, PiLp.norm_single, Real.norm_eq_abs]

lemma spaceAxis_inner (t : ℝ) (y : Space) : inner ℝ (spaceAxis t) y = t * y 0 := by
  simp [spaceAxis, EuclideanSpace.inner_single_left]

lemma extension_one_axis (t : ℝ) :
    extension (fun _ => 1) (spaceAxis t) =
      (2 * Real.pi) • ∫ u in (-1 : ℝ)..1,
        Complex.exp (((2 * Real.pi * t * u : ℝ) : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun u =>
    Complex.exp (((2 * Real.pi * t * u : ℝ) : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have he (R : ℝ) (hR : 0 ≤ R) : ballFourier (spaceAxis t) R =
      ∫ u in (-R)..R, (Real.pi * (R ^ 2 - u ^ 2)) • f u := by
    rw [ballFourier]
    have hk : sphereKernel (spaceAxis t) = fun y => f (y 0) := by
      funext y
      dsimp only [sphereKernel, f]
      rw [spaceAxis_inner]
      congr 1
      push_cast
      ring
    rw [hk, integral_ball_head f hf R hR]
  have hEq : ballFourier (spaceAxis t) =ᶠ[nhds (1 : ℝ)]
      (fun R => ∫ u in (-R)..R, (Real.pi * (R ^ 2 - u ^ 2)) • f u) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with R hR
    exact he R hR.le
  have hD := (hasDerivAt_weighted_slice f hf 1).congr_of_eventuallyEq hEq
  simpa only [mul_one] using (ballFourier_hasDerivAt_one (spaceAxis t)).unique hD

lemma extension_one_axis_formula (t : ℝ) (ht : t ≠ 0) :
    extension (fun _ => 1) (spaceAxis t) =
      ((2 * Real.sin (2 * Real.pi * t) / t : ℝ) : ℂ) := by
  rw [extension_one_axis]
  have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht
  have he := intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I))
    (a := -1) (b := 1) hc
  simp only [mul_neg_one, mul_one] at he
  rw [he, integral_exp_mul_I_eq_sin]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, Complex.ofReal_div]
  field_simp

theorem extension_one_formula (x : Space) (hx : x ≠ 0) :
    extension (fun _ => 1) x =
      ((2 * Real.sin (2 * Real.pi * ‖x‖) / ‖x‖ : ℝ) : ℂ) := by
  have hn : ‖x‖ = ‖spaceAxis ‖x‖‖ := by
    rw [spaceAxis_norm, abs_of_nonneg (norm_nonneg x)]
  let e : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (x - spaceAxis ‖x‖))ᗮ.reflection
  have he : e x = spaceAxis ‖x‖ := Submodule.reflection_sub hn
  have hi := extension_one_isometry e x
  rw [he] at hi
  rw [← hi]
  exact extension_one_axis_formula _ (norm_ne_zero_iff.mpr hx)

open FourierTransform Convolution

def box : ℝ → ℂ := (Icc (-1 : ℝ) 1).indicator (fun _ => 1)

lemma box_measurable : Measurable box := measurable_const.indicator measurableSet_Icc

lemma box_bound (x : ℝ) : ‖box x‖ ≤ 1 := by
  by_cases h : x ∈ Icc (-1 : ℝ) 1 <;> simp [box, h]

lemma box_integrable : Integrable box := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact integrableOn_const (C := (1 : ℂ)) (ne_of_lt (measure_Icc_lt_top : volume (Icc (-1 : ℝ) 1) < ∞))

lemma box_integral : ∫ x, box x = (2 : ℂ) := by
  rw [box, integral_indicator measurableSet_Icc, integral_const]
  simp
  norm_num

lemma box_neg (x : ℝ) : box (-x) = box x := by
  have h : -x ∈ Icc (-1 : ℝ) 1 ↔ x ∈ Icc (-1 : ℝ) 1 := by
    simp only [mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [box, indicator, h]

lemma box_mul_self (x : ℝ) : box x * box x = box x := by
  by_cases h : x ∈ Icc (-1 : ℝ) 1 <;> simp [box, h]

lemma box_fourier {r : ℝ} (hr : r ≠ 0) :
    𝓕 box r = (Real.sin (2 * Real.pi * r) / (Real.pi * r) : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, box]
  simp_rw [← indicator_mul_right (Icc (-1 : ℝ) 1)
    (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * r) * Complex.I)) (fun _ => 1)]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp only [mul_one]
  have he : (fun t : ℝ => Complex.exp ((↑(-2 * Real.pi * t * r) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp ((-2 * Real.pi * r * Complex.I : ℂ) * t)) := by
    ext t
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex (by simp [hr, Real.pi_ne_zero])]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg]
  rw [show (-2 * (Real.pi : ℂ) * r * Complex.I) =
    (-(2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simp only [neg_mul, neg_neg]
  rw [← neg_mul]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  field_simp
  ring

lemma box_fourier_continuous : Continuous (𝓕 box) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by change Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2); fun_prop) box_integrable

lemma box_norm_integral : ∫ x, ‖box x‖ = (2 : ℝ) := by
  simp only [box, norm_indicator_eq_indicator_norm, norm_one]
  rw [integral_indicator measurableSet_Icc, integral_const]
  norm_num

lemma box_fourier_bound (r : ℝ) : ‖𝓕 box r‖ ≤ 2 := by
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) box r).trans_eq box_norm_integral

lemma box_fourier_decay {r : ℝ} (hr : 1 ≤ |r|) : ‖𝓕 box r‖ ≤ 1 / |r| := by
  have hr0 : 0 < |r| := by linarith
  rw [box_fourier (abs_pos.mp hr0), Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_pos Real.pi_pos]
  apply (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)).trans
  apply one_div_le_one_div_of_le hr0
  nlinarith [Real.pi_gt_three]

lemma box_fourier_sq_integrable : Integrable (fun r => (𝓕 box r) ^ 2) := by
  apply (integrable_inv_one_add_sq.const_mul 8).mono'
    (box_fourier_continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with r
  change ‖𝓕 box r ^ 2‖ ≤ 8 * (1 + r ^ 2)⁻¹
  rw [norm_pow]
  have hd : 0 < 1 + r ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hd]
  by_cases hr : |r| ≤ 1
  · have hn := box_fourier_bound r
    have hsq : r ^ 2 ≤ 1 := by nlinarith [sq_abs r, abs_nonneg r]
    nlinarith [sq_nonneg ‖𝓕 box r‖, norm_nonneg (𝓕 box r)]
  · have hr' : 1 ≤ |r| := le_of_not_ge hr
    have hb := box_fourier_decay hr'
    have hr0 : 0 < |r| := lt_of_lt_of_le zero_lt_one hr'
    have hsq : 1 ≤ r ^ 2 := by nlinarith [sq_abs r]
    have hb' : ‖𝓕 box r‖ * |r| ≤ 1 := (le_div_iff₀ hr0).mp hb
    have hs : ‖𝓕 box r‖ ^ 2 * r ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (‖𝓕 box r‖ * |r|), sq_abs r,
        mul_self_le_mul_self (mul_nonneg (norm_nonneg _) (abs_nonneg r)) hb']
    have hn : ‖𝓕 box r‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖𝓕 box r‖]
    nlinarith

noncomputable def tent : ℝ → ℂ := box ⋆[ContinuousLinearMap.mul ℂ ℂ] box

lemma tent_integrable : Integrable tent :=
  box_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) box_integrable

lemma tent_fourier (r : ℝ) : 𝓕 tent r = (𝓕 box r) ^ 2 := by
  rw [tent, Real.fourier_mul_convolution_eq box_integrable box_integrable, pow_two]

lemma tent_fourier_integrable : Integrable (𝓕 tent) := by
  have he : 𝓕 tent = fun r => (𝓕 box r) ^ 2 := funext tent_fourier
  rw [he]
  exact box_fourier_sq_integrable

lemma tent_zero : tent 0 = 2 := by
  change (∫ t, box t * box (0 - t)) = 2
  simpa only [zero_sub, box_neg, box_mul_self] using box_integral

lemma tent_continuousAt_zero : ContinuousAt tent 0 := by
  change ContinuousAt (fun x => ∫ t, box t * box (x - t)) 0
  apply continuousAt_of_dominated (bound := fun t => ‖box t‖)
  · exact Eventually.of_forall (fun x =>
      (box_measurable.mul (box_measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro x
    filter_upwards [] with t
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (box_bound _)
  · exact box_integrable.norm
  · filter_upwards [(volume : Measure ℝ).ae_ne (-1), (volume : Measure ℝ).ae_ne 1] with t ht1 ht2
    have hct : ContinuousAt box (-t) := by
      apply continuous_const.continuousOn.continuousAt_indicator
      rw [frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h; apply ht2; linarith
      · intro h; apply ht1; linarith
    have hc : ContinuousAt box (0 - t) := by simpa using hct
    have hg : ContinuousAt (fun x : ℝ => box (x - t)) 0 :=
      hc.comp (f := fun x : ℝ => x - t) (continuous_id.sub continuous_const).continuousAt
    exact continuousAt_const.mul hg

lemma integral_box_fourier_sq : ∫ r, (𝓕 box r) ^ 2 = (2 : ℂ) := by
  have h := tent_integrable.fourierInv_fourier_eq tent_fourier_integrable tent_continuousAt_zero
  simpa [Real.fourierInv_eq, tent_fourier, tent_zero] using h

def sineSq (r : ℝ) : ℝ := Real.sin (2 * Real.pi * r) ^ 2 / r ^ 2

def sineFourth (r : ℝ) : ℝ := Real.sin (2 * Real.pi * r) ^ 4 / r ^ 2

lemma sineSq_fourier_ae : (fun r => (sineSq r : ℂ)) =ᵐ[volume]
    (fun r => (Real.pi : ℂ) ^ 2 * (𝓕 box r) ^ 2) := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with r hr
  rw [box_fourier hr]
  simp only [sineSq]
  push_cast
  field_simp

lemma sineSq_integrable : Integrable sineSq := by
  have h : Integrable (fun r => (sineSq r : ℂ)) :=
    (box_fourier_sq_integrable.const_mul ((Real.pi : ℂ) ^ 2)).congr sineSq_fourier_ae.symm
  simpa using h.re

lemma sineSq_integral : ∫ r, sineSq r = 2 * Real.pi ^ 2 := by
  have h : ((∫ r, sineSq r : ℝ) : ℂ) = (2 * Real.pi ^ 2 : ℝ) := by
    rw [← integral_complex_ofReal, integral_congr_ae sineSq_fourier_ae,
      integral_const_mul, integral_box_fourier_sq]
    push_cast
    ring
  exact_mod_cast h

lemma sineFourth_identity (r : ℝ) : sineFourth r = sineSq r - sineSq (2 * r) := by
  by_cases hr : r = 0
  · simp [hr, sineFourth, sineSq]
  unfold sineFourth sineSq
  rw [show 2 * Real.pi * (2 * r) = 2 * (2 * Real.pi * r) by ring,
    Real.sin_two_mul]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * r)]

lemma sineFourth_integrable : Integrable sineFourth := by
  apply (sineSq_integrable.sub
    ((integrable_comp_mul_left_iff sineSq (by norm_num : (2 : ℝ) ≠ 0)).2
      sineSq_integrable)).congr
  exact Eventually.of_forall (fun r => (sineFourth_identity r).symm)

lemma sineFourth_integral : ∫ r, sineFourth r = Real.pi ^ 2 := by
  simp_rw [sineFourth_identity]
  rw [integral_sub sineSq_integrable
    ((integrable_comp_mul_left_iff sineSq (by norm_num : (2 : ℝ) ≠ 0)).2 sineSq_integrable),
    Measure.integral_comp_mul_left, sineSq_integral]
  norm_num
  ring

lemma sineFourth_abs (r : ℝ) : sineFourth |r| = sineFourth r := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
  · simp only [abs_of_nonpos hr, sineFourth, mul_neg, Real.sin_neg]
    ring

lemma sineFourth_integral_Ioi : ∫ r in Ioi (0 : ℝ), sineFourth r = Real.pi ^ 2 / 2 := by
  have h := integral_comp_abs (f := sineFourth)
  simp only [sineFourth_abs, sineFourth_integral] at h
  linarith

lemma fourth_radial_density {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * (2 * Real.sin (2 * Real.pi * r) / r) ^ 4 = 16 * sineFourth r := by
  unfold sineFourth
  field_simp
  ring

lemma extension_one_fourth_ae :
    (fun x : Space => ‖extension (fun _ => 1) x‖ ^ 4) =ᵐ[volume]
      (fun x : Space => (2 * Real.sin (2 * Real.pi * ‖x‖) / ‖x‖) ^ 4) := by
  filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
  rw [extension_one_formula x hx, Complex.norm_real, Real.norm_eq_abs]
  rw [← abs_pow, abs_of_nonneg (by positivity)]

lemma extension_one_fourth_integrable :
    Integrable (fun x : Space => ‖extension (fun _ => 1) x‖ ^ 4) := by
  have hp : IntegrableOn (fun r : ℝ => r ^ 2 * (2 * Real.sin (2 * Real.pi * r) / r) ^ 4)
      (Ioi 0) := by
    apply (sineFourth_integrable.const_mul 16).integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (fourth_radial_density (ne_of_gt hr)).symm
  have hi := (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => (2 * Real.sin (2 * Real.pi * r) / r) ^ 4)).2
    (by simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
      smul_eq_mul] using hp)
  exact hi.congr extension_one_fourth_ae.symm

lemma extension_one_fourth_integral :
    ∫ x : Space, ‖extension (fun _ => 1) x‖ ^ 4 = 32 * Real.pi ^ 3 := by
  rw [integral_congr_ae extension_one_fourth_ae,
    integral_fun_norm_addHaar (volume : Measure Space)
      (fun r : ℝ => (2 * Real.sin (2 * Real.pi * r) / r) ^ 4)]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => fourth_radial_density (ne_of_gt hr)),
    integral_const_mul, sineFourth_integral_Ioi]
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

lemma extension_one_fourth_lintegral :
    (∫⁻ x : Space, ENNReal.ofReal (‖extension (fun _ => 1) x‖ ^ 4)) =
      ENNReal.ofReal (32 * Real.pi ^ 3) := by
  rw [← ofReal_integral_eq_lintegral_ofReal extension_one_fourth_integrable
    (Eventually.of_forall (fun x => by positivity)), extension_one_fourth_integral]

lemma extension_congr_ae {g h : Sphere → ℂ} (he : g =ᵐ[surfaceArea] h) :
    extension g = extension h := by
  funext x
  apply integral_congr_ae
  filter_upwards [he] with ω hω
  rw [hω]

lemma eLpNorm_fourth_power (f : Space → ℂ) (hf : AEStronglyMeasurable f volume) :
    (eLpNorm f 4 volume) ^ 4 = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 4) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure Space))
    (f := f) (p := (4 : ℝ≥0)) (by norm_num) hf
  have hn (x : ℝ≥0∞) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by exact ENNReal.rpow_natCast x 4
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  simp only [hn] at h
  rw [h]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem sphere_fourth_power : SphereFourthPower := by
  classical
  intro g hg ⟨B, hB⟩
  let M : ℝ := (eLpNorm g ∞ surfaceArea).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hfin : eLpNorm g ∞ surfaceArea ≠ ∞ := by
    rw [eLpNorm_exponent_top hg.aestronglyMeasurable]
    exact (eLpNormEssSup_lt_top_of_ae_bound (Eventually.of_forall hB)).ne
  have hM : ∀ᵐ ω ∂surfaceArea, ‖g ω‖ ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := surfaceArea)] with ω hω
    have ht := ENNReal.toReal_mono
      (by simpa only [eLpNorm_exponent_top hg.aestronglyMeasurable] using hfin) hω
    simpa [M, eLpNorm_exponent_top hg.aestronglyMeasurable, enorm_eq_nnnorm] using ht
  let h : Sphere → ℂ := fun ω => if ‖g ω‖ ≤ M then g ω else 0
  have hh : Measurable h := Measurable.ite (measurableSet_le hg.norm measurable_const) hg measurable_const
  have hbound : ∀ ω, ‖h ω‖ ≤ M := by
    intro ω
    dsimp [h]
    split_ifs with hw
    · exact hw
    · simpa using hM0
  have he : h =ᵐ[surfaceArea] g := by
    filter_upwards [hM] with ω hω
    simp [h, hω]
  rw [← extension_congr_ae he,
    eLpNorm_fourth_power _ (extension_continuous hh hbound).aestronglyMeasurable]
  calc
    _ ≤ ENNReal.ofReal (M ^ 4) * ∫⁻ x, ENNReal.ofReal (‖extension (fun _ => 1) x‖ ^ 4) :=
      fourth_power_majorant hM0 hh hbound
    _ = ENNReal.ofReal (32 * Real.pi ^ 3) * (eLpNorm g ∞ surfaceArea) ^ 4 := by
      rw [extension_one_fourth_lintegral, ENNReal.ofReal_pow hM0]
      dsimp [M]
      rw [ENNReal.ofReal_toReal hfin, mul_comm]

lemma extension_enorm_le_essSup (g : Sphere → ℂ) (x : Space) :
    ‖extension g x‖ₑ ≤ ENNReal.ofReal (4 * Real.pi) * eLpNorm g ∞ surfaceArea := by
  unfold extension
  calc
    _ ≤ ∫⁻ ω, ‖g ω * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x (ω : Space) : ℂ))‖ₑ ∂surfaceArea :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ : Sphere, eLpNorm g ∞ surfaceArea ∂surfaceArea := by
      apply lintegral_mono_ae
      filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := surfaceArea)] with ω hω
      simpa only [← ofReal_norm, norm_mul, kernel_norm, mul_one]
        using hω.trans eLpNormEssSup_le_eLpNorm_top
    _ = _ := by rw [lintegral_const, surfaceArea_univ, mul_comm]

theorem sphere_restriction_ge_four :
    ∀ p : ℝ, 4 ≤ p → ∃ C : ℝ≥0, ∀ g : Sphere → ℂ,
      Measurable g → (∃ M : ℝ, ∀ ω, ‖g ω‖ ≤ M) →
      eLpNorm (extension g) (ENNReal.ofReal p) volume ≤
        (C : ℝ≥0∞) * eLpNorm g ∞ surfaceArea := by
  intro p hp
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hdiff : 0 ≤ p - 4 := sub_nonneg.mpr hp
  have hinv : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp0)
  let A : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi)
  let B : ℝ≥0∞ := ENNReal.ofReal (32 * Real.pi ^ 3)
  let C : ℝ≥0∞ := (A ^ (p - 4) * B) ^ p⁻¹
  have hA : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hB : B ≠ ∞ := ENNReal.ofReal_ne_top
  have hC : C ≠ ∞ := by
    dsimp [C]
    finiteness
  refine ⟨C.toNNReal, ?_⟩
  intro g hg hbdd
  have hext : AEStronglyMeasurable (extension g) volume :=
    (extension_continuous hg hbdd.choose_spec).aestronglyMeasurable
  rw [ENNReal.coe_toNNReal hC]
  let G := eLpNorm g ∞ surfaceArea
  have hG : G ≠ ∞ := by
    rcases hbdd with ⟨M, hM⟩
    simpa only [G, eLpNorm_exponent_top hg.aestronglyMeasurable] using
      (eLpNormEssSup_lt_top_of_ae_bound (μ := surfaceArea) (Filter.Eventually.of_forall hM)).ne
  have hpoint : ∀ x, ‖extension g x‖ₑ ≤ A * G := extension_enorm_le_essSup g
  have hfour : (∫⁻ x, ‖extension g x‖ₑ ^ (4 : ℕ)) ≤ B * G ^ (4 : ℕ) := by
    have h := sphere_fourth_power g hg hbdd
    rw [eLpNorm_fourth_power _ hext] at h
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  have hsplit : ∀ x, ‖extension g x‖ₑ ^ p ≤
      (A * G) ^ (p - 4) * ‖extension g x‖ₑ ^ (4 : ℕ) := by
    intro x
    calc
      ‖extension g x‖ₑ ^ p =
          ‖extension g x‖ₑ ^ (p - 4) * ‖extension g x‖ₑ ^ (4 : ℝ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hdiff (by norm_num), sub_add_cancel]
      _ ≤ (A * G) ^ (p - 4) * ‖extension g x‖ₑ ^ (4 : ℝ) :=
        mul_le_mul_left (ENNReal.rpow_le_rpow (hpoint x) hdiff) _
      _ = _ := by rw [ENNReal.rpow_ofNat]
  have integral_bound : (∫⁻ x, ‖extension g x‖ₑ ^ p) ≤ (A ^ (p - 4) * B) * G ^ p := by
    calc
      _ ≤ ∫⁻ x, (A * G) ^ (p - 4) * ‖extension g x‖ₑ ^ (4 : ℕ) :=
        lintegral_mono hsplit
      _ = (A * G) ^ (p - 4) * (∫⁻ x, ‖extension g x‖ₑ ^ (4 : ℕ)) :=
        lintegral_const_mul' _ _ (by finiteness)
      _ ≤ (A * G) ^ (p - 4) * (B * G ^ (4 : ℕ)) := mul_le_mul_right hfour _
      _ = (A ^ (p - 4) * B) * (G ^ (p - 4) * G ^ (4 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hdiff, ENNReal.rpow_ofNat]
        ring
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hdiff (by norm_num), sub_add_cancel]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
    ENNReal.ofReal_ne_top hext, ENNReal.toReal_ofReal hp0.le, one_div]
  calc
    _ ≤ ((A ^ (p - 4) * B) * G ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow integral_bound hinv
    _ = C * G := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

end EllipticCapacity

end

end OAI
