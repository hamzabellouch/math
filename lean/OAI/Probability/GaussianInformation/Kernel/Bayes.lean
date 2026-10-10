import Mathlib
import OAI.Probability.GaussianInformation.Kernel.SampleEquivalence

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity Sphere

noncomputable def mass {α : Type*} [MeasurableSpace α] (ν : Measure α) (r : α → ℝ) : ℝ := ∫ s,r s ∂ν
noncomputable def post {α : Type*} [MeasurableSpace α] (ν : Measure α) (r : α → ℝ) : Measure α :=
  ν.withDensity (fun s => ENNReal.ofReal (r s/mass ν r))

lemma integrable_rule {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) : Integrable r ν :=
  integrable_bounded_measurable ν r hr (fun s => by rw [abs_of_nonneg (hr0 s)]; exact hr1 s)

lemma mass_bounds {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (r : α → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) : ε ≤ mass ν r ∧ mass ν r ≤ 1 := by
  have hi := integrable_rule ν r hr (fun s => hε.le.trans (hrε s)) hr1
  constructor
  · simpa [mass] using integral_mono (integrable_const ε) hi hrε
  · simpa [mass] using integral_mono hi (integrable_const 1) hr1

lemma post_probability {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) : IsProbabilityMeasure (post ν r) := by
  have hi := integrable_rule ν r hr hr0 hr1
  constructor
  rw [post,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun s => div_nonneg (hr0 s) ha.le)),
    integral_div]
  change ENNReal.ofReal (mass ν r/mass ν r)=1
  simp [ha.ne']

lemma post_integral {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (ha : 0 < mass ν r)
    (g : α → ℝ) : (∫ s,g s ∂post ν r) = (∫ s,r s*g s ∂ν)/mass ν r := by
  rw [post,integral_withDensity_eq_integral_toReal_smul (hr.div_const _).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hr0 _) ha.le),smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

lemma post_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (r : α → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (1/mass ν r) • ν :=
  density_bounded ν _ (fun s => div_le_div_of_nonneg_right (hr1 s) ha.le)

lemma post_bounded {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (H/mass ν r) • sphereProbability d := by
  calc
    _ ≤ ENNReal.ofReal (1/mass ν r) • ν := post_le ν r hr1 ha
    _ ≤ ENNReal.ofReal (1/mass ν r) • (ENNReal.ofReal H • sphereProbability d) := smul_le_smul_left _ hν
    _ = _ := by rw [smul_smul,← ENNReal.ofReal_mul' hH.le]; congr 2; ring

lemma post_density {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (f r : α → ℝ) (hf : Measurable f) (hf0 : ∀ s,0 ≤ f s) (hr : Measurable r)
    (hν : ν=μ.withDensity (fun s => ENNReal.ofReal (f s))) :
    post ν r = μ.withDensity (fun s => ENNReal.ofReal (f s*r s/mass ν r)) := by
  unfold post
  nth_rw 1 [hν]
  rw [← withDensity_mul _ hf.ennreal_ofReal (hr.div_const _).ennreal_ofReal]
  congr 1
  ext s
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (hf0 s),mul_div_assoc]

noncomputable def clippedJ {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : ℝ :=
  max ((1/2:ℝ)^(2*(d/16))) (J ν s).toReal

lemma clippedJ_measurable {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] :
    Measurable (clippedJ ν) := measurable_const.max (measurable_J ν).ennreal_toReal
lemma clippedJ_pos {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : 0 < clippedJ ν s :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)
lemma clippedJ_eq {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) : clippedJ ν s=(J ν s).toReal :=
  max_eq_right (J_real_bounds hd ν hH hν s hs).1

lemma integrable_log_clippedJ {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BoundedDensity ν) (μ : Measure (Ambient d)) [IsFiniteMeasure μ] :
    Integrable (fun s => Real.log (clippedJ ν s)) μ := by
  obtain ⟨H,hH,hνH⟩ := hν
  apply integrable_log_of_bounds μ _ (clippedJ_measurable ν)
    (b := max ((1/2:ℝ)^(2*(d/16))) (H*(1+9*3^d*2^((d-1)+2*(d/16)+1))))
    (by positivity : (0:ℝ) < (1/2:ℝ)^(2*(d/16)))
  filter_upwards [] with s
  refine ⟨le_max_left _ _, max_le_max le_rfl ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (bounded_J hd ν hH hνH s)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

noncomputable def referenceWeight {d : ℕ} (ν : Measure (Ambient d)) (r : Ambient d → ℝ)
    (s : Ambient d) : ℝ := r s/(mass ν r*clippedJ (post ν r) s)

lemma xlog_posterior_identity {f r a j : ℝ} (hr : 0 < r) (ha : 0 < a) (hj : 0 < j) :
    a*(xlog (f*r/a)-(f*r/a)*Real.log j) =
      r*xlog f+f*r*Real.log (r/(a*j)) := by
  rw [show f*r/a=f*(r/a) by ring,xlog_mul]
  simp only [xlog]
  rw [Real.log_div hr.ne' ha.ne',Real.log_div hr.ne' (mul_ne_zero ha.ne' hj.ne'),
    Real.log_mul ha.ne' hj.ne']
  field_simp
  ring

lemma weighted_Phi_identity {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (f : Ambient d → ℝ) (hf : Measurable f) (hf0 : ∀ s,0 ≤ f s)
    {H : ℝ} (hH : 0 < H) (hfH : ∀ s,f s ≤ H)
    (hν : ν=(sphereProbability d).withDensity (fun s => ENNReal.ofReal (f s)))
    (r : Ambient d → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    mass ν r*Phi (post ν r) =
      (∫ s,r s*xlog (f s) ∂sphereProbability d)+
        ∫ s,r s*Real.log (referenceWeight ν r s) ∂ν := by
  have hr0 (s : Ambient d) : 0 ≤ r s := hε.le.trans (hrε s)
  have hrpos (s : Ambient d) : 0 < r s := hε.trans_le (hrε s)
  have ha := hε.trans_le (mass_bounds ν r hr hε hrε hr1).1
  have hνb : ν ≤ ENNReal.ofReal H • sphereProbability d := by rw [hν]; exact density_bounded _ _ hfH
  have hp := post_bounded ν hH hνb r hr1 ha
  have := post_probability ν r hr hr0 hr1 ha
  have hpb : BoundedDensity (post ν r) := ⟨H/mass ν r,div_pos hH ha,hp⟩
  let F : Ambient d → ℝ := fun s => f s*r s/mass ν r
  have hF : Measurable F := (hf.mul hr).div_const _
  have hF0 (s : Ambient d) : 0 ≤ F s := div_nonneg (mul_nonneg (hf0 s) (hr0 s)) ha.le
  have hFH (s : Ambient d) : F s ≤ H/mass ν r := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact (mul_le_mul_of_nonneg_left (hr1 s) (hf0 s)).trans (by simpa using hfH s)
  have hpost : post ν r=(sphereProbability d).withDensity (fun s => ENNReal.ofReal (F s)) :=
    post_density _ ν f r hf hf0 hr hν
  have hlogr : Integrable (fun s => Real.log (r s)) (sphereProbability d) :=
    integrable_log_of_bounds _ _ hr hε (ae_of_all _ (fun s => ⟨hrε s,hr1 s⟩))
  have hlogj := integrable_log_clippedJ hd (post ν r) hpb (sphereProbability d)
  have hlogx : Integrable (fun s => Real.log (referenceWeight ν r s)) (sphereProbability d) := by
    have he : (fun s => Real.log (referenceWeight ν r s)) =
        (fun s => Real.log (r s)-Real.log (mass ν r)-Real.log (clippedJ (post ν r) s)) := by
      ext s
      rw [referenceWeight,Real.log_div (hrpos s).ne' (mul_ne_zero ha.ne' (clippedJ_pos _ _).ne'),
        Real.log_mul ha.ne' (clippedJ_pos _ _).ne']
      ring
    rw [he]
    exact (hlogr.sub (integrable_const _)).sub hlogj
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hleft := hix.bdd_mul hr.aestronglyMeasurable (ae_of_all _ (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hr0 s)]; exact hr1 s))
  have hxright : Integrable (fun s => f s*(r s*Real.log (referenceWeight ν r s))) (sphereProbability d) :=
    (hlogx.bdd_mul hr.aestronglyMeasurable (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hr0 s)]; exact hr1 s))).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ (fun s => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 s)]; exact hfH s))
  rw [Phi_density_formula hd F hF hF0 hFH (post ν r) hpb hpost,← integral_const_mul]
  have hνint : (∫ s,r s*Real.log (referenceWeight ν r s) ∂ν) =
      ∫ s,f s*(r s*Real.log (referenceWeight ν r s)) ∂sphereProbability d := by
    rw [hν,integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [hνint,← integral_add hleft hxright]
  apply integral_congr_ae
  filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
  rw [referenceWeight,clippedJ_eq hd (post ν r) (div_pos hH ha) hp s hs]
  simpa only [F,mul_assoc] using xlog_posterior_identity (f := f s) (hrpos s) ha
    (lt_of_lt_of_le (by positivity : (0:ℝ)<(1/2:ℝ)^(2*(d/16)))
      (J_real_bounds hd (post ν r) (div_pos hH ha) hp s hs).1)

end KernelPotential.Bayes

end OAI
