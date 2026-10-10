import Mathlib
import OAI.Geometry.BallPacking.Campanato.MeasureEnergy

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def translatedSquare (c : Plane) (r : ℝ) : Measure Plane :=
  Measure.map (fun z => z+c) (squareMeasure (-r) r)

instance translatedSquare_finite (c : Plane) (r : ℝ) : IsFiniteMeasure (translatedSquare c r) := by
  unfold translatedSquare
  infer_instance

lemma translatedSquare_mass (c : Plane) {r : ℝ} (hr : 0≤r) :
    (translatedSquare c r).real univ=(2*r)^2 := by
  rw [translatedSquare,Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  change (squareMeasure (-r) r).real univ=(2*r)^2
  rw [squareMeasure_mass (by linarith)]
  ring

lemma translatedSquare_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (c : Plane) (r : ℝ) :
    Integrable f (translatedSquare c r) := by
  unfold translatedSquare
  apply ((Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding.integrable_map_iff).mpr
  exact continuous_square_integrable (hf.comp (continuous_id.add continuous_const)) _ _

lemma translatedSquare_average (c : Plane) (r : ℝ) (v : Plane → Phase n) :
    phaseAverage (translatedSquare c r) v=
      phaseAverage (squareMeasure (-r) r) (fun z => v (z+c)) := by
  have he : MeasurableEmbedding (fun z : Plane => z+c) := (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  unfold phaseAverage translatedSquare
  rw [he.integral_map]
  congr 1
  rw [Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  rfl

lemma translatedSquare_le {c : Plane} {r R : ℝ} (hrr : ‖c‖+r≤R) :
    translatedSquare c r≤ squareMeasure (-R) R := by
  have hsub : (Icc (-r) r) ×ˢ (Icc (-r) r)⊆
      (fun z : Plane => z+c) ⁻¹' ((Icc (-R) R) ×ˢ (Icc (-R) R)) := by
    intro z hz
    have hc1 := norm_fst_le c
    have hc2 := norm_snd_le c
    have hc1' := abs_le.mp hc1
    have hc2' := abs_le.mp hc2
    change (z.1+c.1,z.2+c.2)∈(Icc (-R) R) ×ˢ (Icc (-R) R)
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  have hh := Measure.map_mono (Measure.restrict_mono hsub (le_refl (volume : Measure Plane)))
    (show Measurable (fun z : Plane => z+c) by fun_prop)
  rw [←Measure.restrict_map (by fun_prop) (measurableSet_Icc.prod measurableSet_Icc),
    (measurePreserving_add_right (volume : Measure Plane) c).map_eq] at hh
  simpa only [translatedSquare,squareMeasure_eq] using hh

lemma translated_square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {c : Plane} {r R : ℝ} (hr : 0<r) (hR : 0<R) (hrr : ‖c‖+r≤R) :
    ‖phaseAverage (squareMeasure (-R) R) v-phaseAverage (translatedSquare c r) v‖^2≤
      ((2*r)^2)⁻¹*(8*(2*R)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
  have hvi := translatedSquare_integrable hv.continuous c r
  have hve := translatedSquare_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c r
  have hm : 0<(translatedSquare c r).real univ := by rw [translatedSquare_mass c hr.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure (-R) R) v)
  rw [translatedSquare_mass c hr.le] at hj
  have hii : Integrable (fun z => stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z)) (squareMeasure (-R) R) :=
    continuous_square_integrable
      (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
        (continuous_const.sub hv.continuous)) _ _
  have hmono := integral_mono_measure (translatedSquare_le hrr)
    (Eventually.of_forall (fun z => stdDot_nonneg (phaseAverage (squareMeasure (-R) R) v-v z))) hii
  have hp := square_poincare hv (a := -R) (b := R) (by linarith)
  have hp' : (∫ z,stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z) ∂squareMeasure (-R) R)≤
      8*(R-(-R))^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
    simpa only [stdDot_sub_swap (phaseAverage (squareMeasure (-R) R) v)] using hp
  have hh := (norm_sq_le_stdDot _).trans (hj.trans
    (mul_le_mul_of_nonneg_left (hmono.trans hp') (by positivity)))
  simpa only [sub_neg_eq_add,←two_mul,mul_assoc] using hh


lemma correction_norm_triangle (a b c : Phase n) : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
  simpa only [dist_eq_norm] using dist_triangle a b c

lemma square_dirichlet_le_total {w : ℂ → Phase n}
    (hi : Integrable (dirichletEnergy w)) (r : ℝ) :
    (∫ z,dirichletEnergy w z ∂squareMeasure (-r) r)≤∫ z,dirichletEnergy w z := by
  rw [squareMeasure_eq]
  exact setIntegral_le_integral hi (Eventually.of_forall (dirichletEnergy_nonneg w))

lemma centered_dirichlet_integrable {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) (c : ℂ) :
    Integrable (dirichletEnergy (centeredCurve w c)) := by
  have hh := (measurePreserving_add_right volume (Complex.equivRealProdCLM c)).integrable_comp_of_integrable hi
  change Integrable (fun z => dirichletEnergy (centeredCurve w c) z)
  simp_rw [dirichletEnergy_centered hw]
  exact hh

lemma centered_dirichlet_integral {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w) (c : ℂ) :
    (∫ z,dirichletEnergy (centeredCurve w c) z)=∫ z,dirichletEnergy w z := by
  simp only [dirichletEnergy_centered hw,integral_add_right_eq_self]

def curveSquareAverage (w : ℂ → Phase n) (c : ℂ) (r : ℝ) : Phase n :=
  phaseAverage (squareMeasure (-r) r) (realCurve (centeredCurve w c))

lemma curveSquareAverage_translated (w : ℂ → Phase n) (c : ℂ) (r : ℝ) :
    curveSquareAverage w c r=phaseAverage (translatedSquare (Complex.equivRealProdCLM c) r) (realCurve w) := by
  rw [translatedSquare_average,curveSquareAverage,realCurve_centered]

lemma curveSquareAverage_zero (w : ℂ → Phase n) (r : ℝ) :
    curveSquareAverage w 0 r=phaseAverage (squareMeasure (-r) r) (realCurve w) := by
  unfold curveSquareAverage
  congr 2
  funext z
  simp only [centeredCurve,add_zero]

lemma growing_square_step {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) (c : ℂ) {r : ℝ} (hr : 0<r) :
    ‖curveSquareAverage w c (4*r)-curveSquareAverage w c r‖≤Real.sqrt (128*D) := by
  have hq := quarter_square_mean_norm (realCurve_smooth (centeredCurve_smooth hw c))
    (r := 4*r) (by positivity)
  have ht := (square_dirichlet_le_total (centered_dirichlet_integrable hw hi c) (4*r))
  rw [centered_dirichlet_integral hw] at ht
  have hm := mul_le_mul_of_nonneg_left (ht.trans he) (by norm_num : (0:ℝ)≤128)
  have hb : ‖curveSquareAverage w c (4*r)-curveSquareAverage w c r‖^2≤128*D := by
    rw [show 4*r/4=r by ring] at hq
    exact hq.trans hm
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hb

lemma growing_square_telescope {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) (c : ℂ) {r : ℝ} (hr : 0<r) (k : ℕ) :
    ‖curveSquareAverage w c (r*4^k)-curveSquareAverage w c r‖≤(k:ℝ)*Real.sqrt (128*D) := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hs := growing_square_step hw hi hD he c (r := r*4^k) (by positivity)
    have hid : r*4^(k+1)=4*(r*4^k) := by rw [pow_succ]; ring
    rw [hid]
    have ht := correction_norm_triangle (curveSquareAverage w c (4*(r*4^k)))
      (curveSquareAverage w c (r*4^k)) (curveSquareAverage w c r)
    push_cast
    nlinarith only [ht,hs,hk]

lemma neighboring_growing_means {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) {c : ℂ} {r : ℝ} (hr : 0<r)
    (hc : ‖Complex.equivRealProdCLM c‖≤r) :
    ‖curveSquareAverage w c r-curveSquareAverage w 0 r‖≤2*Real.sqrt (128*D) := by
  have hq := translated_square_means_energy (realCurve_smooth hw) hr
    (R := 4*r) (by positivity) (c := Complex.equivRealProdCLM c) (by linarith)
  have hid : ((2*r)^2)⁻¹*(8*(2*(4*r))^2)=(128:ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hid] at hq
  have hm := mul_le_mul_of_nonneg_left ((square_dirichlet_le_total hi (4*r)).trans he)
    (by norm_num : (0:ℝ)≤128)
  have hb : ‖curveSquareAverage w 0 (4*r)-curveSquareAverage w c r‖≤Real.sqrt (128*D) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [curveSquareAverage_zero,curveSquareAverage_translated]
    exact hq.trans hm
  have hs := growing_square_step hw hi hD he 0 hr
  have ht := correction_norm_triangle (curveSquareAverage w c r) (curveSquareAverage w 0 (4*r))
    (curveSquareAverage w 0 r)
  rw [norm_sub_rev (curveSquareAverage w c r) (curveSquareAverage w 0 (4*r))] at ht
  linarith

lemma correction_growth_by_scales {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D L : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) {r : ℝ} (hr : 0<r)
    (hlocal : ∀ c : ℂ,‖w c-curveSquareAverage w c r‖≤L)
    (k : ℕ) (c : ℂ) (hc : ‖Complex.equivRealProdCLM c‖≤r*4^k) :
    ‖w c-w 0‖≤2*L+2*((k:ℝ)+1)*Real.sqrt (128*D) := by
  have htc := growing_square_telescope hw hi hD he c hr k
  have ht0 := growing_square_telescope hw hi hD he 0 hr k
  have hnb := neighboring_growing_means hw hi hD he (by positivity) hc
  have h1 := correction_norm_triangle (w c) (curveSquareAverage w c r) (w 0)
  have h2 := correction_norm_triangle (curveSquareAverage w c r) (curveSquareAverage w c (r*4^k)) (w 0)
  have h3 := correction_norm_triangle (curveSquareAverage w c (r*4^k)) (curveSquareAverage w 0 (r*4^k)) (w 0)
  have h4 := correction_norm_triangle (curveSquareAverage w 0 (r*4^k)) (curveSquareAverage w 0 r) (w 0)
  rw [norm_sub_rev (curveSquareAverage w c r) (curveSquareAverage w c (r*4^k))] at h2
  rw [norm_sub_rev (curveSquareAverage w 0 r) (w 0)] at h4
  linarith [hlocal c,hlocal 0]


lemma realProd_norm_le (c : ℂ) : ‖Complex.equivRealProdCLM c‖≤‖c‖ := by
  change max ‖c.re‖ ‖c.im‖≤‖c‖
  exact max_le (Complex.abs_re_le_norm c) (Complex.abs_im_le_norm c)

lemma translated_camp_mean_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (he : radialCurveEnergy u ((1/16)^k)≤B*θ^k)
    {c : ℂ} (hc : ‖c‖≤campRadius (k+1)) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1)))
        (realCurve (centeredCurve u c))‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc' : ‖Complex.equivRealProdCLM c‖+campRadius (k+1)≤campRadius k := by
    have hh := (realProd_norm_le c).trans hc
    rw [campRadius_succ] at hh ⊢
    linarith [campRadius_pos k]
  have hh := translated_square_means_energy (realCurve_smooth hu)
    (campRadius_pos (k+1)) (campRadius_pos k) hc'
  rw [translatedSquare_average,←realCurve_centered] at hh
  have hid : ((2*campRadius (k+1))^2)⁻¹*(8*(2*campRadius k)^2)=(128:ℝ) := by
    rw [campRadius_succ]
    field_simp [(campRadius_pos k).ne']
    ring
  rw [hid] at hh
  have hr := square_dirichlet_le_radial hu (campRadius_pos k).le (by positivity : (0:ℝ)<(1/16)^k) (campRadius_sq k)
  apply geometric_sqrt_norm_bound hB hθ k
  exact hh.trans ((mul_le_mul_of_nonneg_left (hr.trans he) (by norm_num)).trans_eq (by ring))

lemma centeredCurve_zero (u : ℂ → Phase n) : centeredCurve u 0=u := by
  funext z
  simp only [centeredCurve,add_zero]

lemma centeredCurve_centered (u : ℂ → Phase n) (p q : ℂ) :
    centeredCurve (centeredCurve u p) q=centeredCurve u (q+p) := by
  funext z
  simp only [centeredCurve,add_assoc]

lemma campanato_oscillation_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {c : ℂ} (hc : ‖c‖≤campRadius (k+1)) :
    ‖u c-u 0‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have hden : 0<1-Real.sqrt θ := by linarith
  have he0 : ∀ j : ℕ,radialCurveEnergy u ((1/16)^j)≤B*θ^j := by
    intro j
    simpa only [centeredCurve_zero] using he 0 j
  have hpc := campanato_point_mean (centeredCurve_smooth hu c) hB hθ hθ1 (he c) (k+1)
  have hp0 := campanato_point_mean hu hB hθ hθ1 he0 (k+1)
  have hmc := translated_camp_mean_bound hu hB hθ k (he0 k) hc
  have hm0 := translated_camp_mean_bound hu hB hθ k (he0 k) (c := 0) (by simpa using (campRadius_pos (k+1)).le)
  rw [centeredCurve_zero] at hm0
  simp only [centeredCurve,zero_add] at hpc
  let m := phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)
  let m0 := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve u)
  let mc := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve (centeredCurve u c))
  have htri : ‖u c-u 0‖≤‖mc-u c‖+‖m-mc‖+‖m-m0‖+‖m0-u 0‖ := by
    have h1 := dist_triangle (u c) mc (u 0)
    have h2 := dist_triangle mc m (u 0)
    have h3 := dist_triangle m m0 (u 0)
    simp only [dist_eq_norm] at h1 h2 h3
    rw [norm_sub_rev (u c) mc] at h1
    rw [norm_sub_rev mc m] at h2
    linarith
  have ht : ‖u c-u 0‖≤
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k) := by
    dsimp [m,m0,mc] at htri
    linarith only [htri,hpc,hp0,hmc,hm0]
  have hid : 2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k)=
      2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
    rw [pow_succ]
    field_simp
    ring
  exact ht.trans_eq hid

lemma campanato_oscillation {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {p q : ℂ} (hpq : ‖q-p‖≤campRadius (k+1)) :
    ‖u q-u p‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hh := campanato_oscillation_zero (centeredCurve_smooth hu p) hB hθ hθ1
    (fun c j => by simpa only [centeredCurve_centered] using he (c+p) j) k hpq
  simpa only [centeredCurve,sub_add_cancel,zero_add] using hh


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma energy_uniform_modulus {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
      ∀ (u : ℂ → Phase n),ContDiff ℝ ∞ u →
        (∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) →
        ∀ p q : ℂ,dist p q<δ →dist (u p) (u q)<ε := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have ht : Tendsto (fun k : ℕ => 2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg θ) hroot).const_mul
      (2*Real.sqrt (128*B))).div_const (1-Real.sqrt θ)
    simpa only [mul_zero,zero_div] using hh
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨campRadius (k+1),campRadius_pos (k+1),?_⟩
  intro u hu he p q hpq
  have hpq' : ‖q-p‖≤campRadius (k+1) := by
    simpa only [dist_eq_norm,norm_sub_rev] using hpq.le
  have hh := campanato_oscillation hu hB hθ hθ1 he k hpq'
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt hk

lemma energy_decay_uniformContinuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) :
    UniformContinuous u := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 hε
  exact ⟨δ,hδ,fun p q hpq => hh u hu he p q hpq⟩


def dilatedCurve (u : ℂ → Phase n) (c : ℂ) : ℂ → Phase n := fun z => u (c*z)

lemma dilatedCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (dilatedCurve u c) := hu.comp (contDiff_const.mul contDiff_id)

lemma dilatedCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c z : ℂ) :
    fderiv ℝ (dilatedCurve u c) z=(fderiv ℝ u (c*z)).comp (ContinuousLinearMap.mul ℝ ℂ c) := by
  have hh := (hu.differentiable (by simp) (c*z)).hasFDerivAt.comp z
    (ContinuousLinearMap.mul ℝ ℂ c).hasFDerivAt
  change HasFDerivAt (dilatedCurve u c) _ z at hh
  exact hh.fderiv

lemma dilatedCurve_CR {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hCR : ∀ z,PseudoHolomorphicAt J u z) (c z : ℂ) :
    PseudoHolomorphicAt J (dilatedCurve u c) z := by
  refine ⟨(dilatedCurve_smooth hu c).differentiable (by simp) z,?_⟩
  intro w
  rw [dilatedCurve_fderiv hu]
  simp only [ContinuousLinearMap.comp_apply,dilatedCurve]
  change fderiv ℝ u (c*z) (c*(Complex.I*w))=J (u (c*z)) (fderiv ℝ u (c*z) (c*w))
  rw [show c*(Complex.I*w)=Complex.I*(c*w) by ring]
  exact (hCR (c*z)).2 (c*w)

lemma dilatedCurve_slope {u : ℂ → Phase n} {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    {c : ℂ} (hc : c≠0) :
    Tendsto (fun z : ℂ => z⁻¹ • dilatedCurve u c z) (cocompact ℂ) (𝓝 (c • a)) := by
  have hh := (ha.comp (Filter.tendsto_cocompact_mul_left₀ hc)).const_smul c
  apply hh.congr'
  exact Eventually.of_forall fun z => by
    dsimp only [Function.comp_def,dilatedCurve]
    rw [smul_smul]
    congr 1
    rw [mul_inv_rev,←mul_assoc,mul_comm c z⁻¹,mul_assoc,mul_inv_cancel₀ hc,mul_one]

lemma AffineLineCurve.dilate {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) {c : ℂ} (hc : c≠0) :
    AffineLineCurve J p (u c) (dilatedCurve u c) := by
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  refine ⟨dilatedCurve_smooth hu.1 c,dilatedCurve_CR hu.1 hu.2.1 c,?_,?_,
    c • a,smul_ne_zero hc ha,dilatedCurve_slope hlim hc⟩
  · simpa only [dilatedCurve,mul_zero] using hu.2.2.1
  · simp only [dilatedCurve,mul_one]


def slopeScale (a : Phase n) : ℝ := (Real.sqrt (stdDot n a a))⁻¹

lemma slopeScale_pos {a : Phase n} (ha : a≠0) : 0<slopeScale a := by
  unfold slopeScale
  exact inv_pos.mpr (Real.sqrt_pos.mpr (stdDot_pos ha))

lemma normalizedSlope_unit {a : Phase n} (ha : a≠0) :
    stdDot n ((slopeScale a) • a) ((slopeScale a) • a)=1 := by
  simp only [map_smul,smul_apply,smul_eq_mul,slopeScale]
  have hs : (Real.sqrt (stdDot n a a))^2=stdDot n a a := Real.sq_sqrt (stdDot_nonneg a)
  have hp : 0<Real.sqrt (stdDot n a a) := Real.sqrt_pos.mpr (stdDot_pos ha)
  field_simp
  nlinarith

lemma exact_line_local_energy_of_slope {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ C M θ : ℝ,0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ a : Phase n,Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        ∀ (c : ℂ) (k : ℕ),radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤
          (C+M*stdDot n a a)*θ^k := by
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_uniform_local_energy hJs hJ hJc hST hT hout
  refine ⟨C,M,θ,hC,hM,hθ,hθ1,?_⟩
  intro t ht p q u hu a ha c k
  obtain ⟨a',ha',hlim,hbound⟩ := he t ht p q u hu
  have haa : a'=a := tendsto_nhds_unique hlim ha
  subst a'
  simpa only [one_div_pow,mul_comm] using hbound c k

lemma exact_normalized_line_energy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ B θ : ℝ,0<B ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ a : Phase n,a≠0 → Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        ∀ (c : ℂ) (k : ℕ),
          radialCurveEnergy (centeredCurve (dilatedCurve u (slopeScale a)) c) ((1/16)^k)≤B*θ^k := by
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope hJs hJ hJc hST hT hout
  refine ⟨C+M,θ,by linarith,hθ,hθ1,?_⟩
  intro t ht p q u hu a ha hlim c k
  have hs : (slopeScale a : ℂ)≠0 := by exact_mod_cast (slopeScale_pos ha).ne'
  have hlu := dilatedCurve_slope hlim hs
  have he' := he t ht p (u (slopeScale a)) (dilatedCurve u (slopeScale a)) (hu.dilate hs)
    ((slopeScale a : ℂ) • a) hlu c k
  have hnorm : stdDot n ((slopeScale a : ℂ) • a) ((slopeScale a : ℂ) • a)=1 := by
    simpa only [Complex.coe_smul] using normalizedSlope_unit ha
  simpa only [hnorm,mul_one] using he'


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma complex_norm_le_two_plane_norm (z : Plane) : ‖Complex.equivRealProdCLM.symm z‖≤2*‖z‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm z)
  simp only [Complex.equivRealProdCLM_symm_apply_re,Complex.equivRealProdCLM_symm_apply_im] at hh
  have h1 := norm_fst_le z
  have h2 := norm_snd_le z
  simp only [Real.norm_eq_abs] at h1 h2
  exact hh.trans (by linarith)

lemma unit_slope_norm_le {a : Phase n} (ha : stdDot n a a=1) : ‖a‖≤1 := by
  have hh := norm_sq_le_stdDot a
  rw [ha] at hh
  nlinarith [norm_nonneg a]

lemma correction_local_average {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    ∃ r : ℝ,0<r ∧ ∀ (u : ℂ → Phase n),ContDiff ℝ ∞ u →
      (∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) →
      ∀ a : Phase n,stdDot n a a=1 →∀ c : ℂ,
        ‖affineCorrection u a c-curveSquareAverage (affineCorrection u a) c r‖≤2 := by
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 (by norm_num : (0:ℝ)<1)
  let r : ℝ := min (δ/4) (1/4)
  have hr : 0<r := lt_min (by positivity) (by norm_num)
  have hrδ : 2*r<δ := by have hh := min_le_left (δ/4) (1/4:ℝ); dsimp [r]; linarith
  have hr1 : 2*r≤1 := by have hh := min_le_right (δ/4) (1/4:ℝ); dsimp [r]; linarith
  refine ⟨r,hr,?_⟩
  intro u hu he a ha c
  have hm : 0<(squareMeasure (-r) r).real univ := by
    rw [squareMeasure_mass (by linarith)]
    exact sq_pos_of_pos (by linarith)
  have hi := continuous_square_integrable (realCurve_smooth
    (centeredCurve_smooth (affineCorrection_smooth hu a) c)).continuous (-r) r
  have hb : ∀ᵐ z ∂squareMeasure (-r) r,
      ‖affineCorrection u a c-realCurve (centeredCurve (affineCorrection u a) c) z‖≤2 := by
    filter_upwards [square_ae_mem (-r) r] with z hz
    have hzn : ‖Complex.equivRealProdCLM.symm z‖≤2*r :=
      (complex_norm_le_two_plane_norm z).trans (mul_le_mul_of_nonneg_left (plane_norm_le_square hz) (by norm_num))
    have hd : dist c (Complex.equivRealProdCLM.symm z+c)<δ := by
      rw [dist_eq_norm,show c-(Complex.equivRealProdCLM.symm z+c)=-(Complex.equivRealProdCLM.symm z) by abel,norm_neg]
      exact hzn.trans_lt hrδ
    have huosc := hmod u hu he c (Complex.equivRealProdCLM.symm z+c) hd
    rw [dist_eq_norm] at huosc
    have han : ‖a‖≤1 := unit_slope_norm_le ha
    have hzsmul : ‖Complex.equivRealProdCLM.symm z • a‖≤1 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left han (norm_nonneg _)).trans (by simpa only [mul_one] using hzn.trans hr1)
    have hid : affineCorrection u a c-affineCorrection u a (Complex.equivRealProdCLM.symm z+c)=
        (u c-u (Complex.equivRealProdCLM.symm z+c))+Complex.equivRealProdCLM.symm z • a := by
      simp only [affineCorrection,add_smul]
      abel
    change ‖affineCorrection u a c-affineCorrection u a (Complex.equivRealProdCLM.symm z+c)‖≤2
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  have hh := phaseAverage_norm_le hm hb
  rw [phaseAverage_const_sub hi hm] at hh
  exact hh


lemma scale_growth_squared {w : ℂ → Phase n} {p : Phase n} {r A : ℝ}
    (hr : 0<r) (hA : 0≤A)
    (hg : ∀ (k : ℕ) (c : ℂ),‖Complex.equivRealProdCLM c‖≤r*4^k →
      ‖w c-p‖≤4+2*((k:ℝ)+1)*A) (c : ℂ) :
    ‖w c-p‖^2≤((4+4*A)^2/r)*(‖c‖+r) := by
  have hx : 1≤‖c‖/r+1 := by linarith [div_nonneg (norm_nonneg c) hr.le]
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<4)
  have hc : ‖Complex.equivRealProdCLM c‖≤r*4^(k+1) := by
    have hcn : ‖c‖<r*4^(k+1) := by
      have hh : ‖c‖/r<4^(k+1) := by linarith
      have htt := (div_lt_iff₀ hr).mp hh
      simpa only [mul_comm] using htt
    exact (Complex.equivRealProd_apply_le c).trans hcn.le
  have hh := hg (k+1) c hc
  have hnat : (k:ℝ)+2≤2*(2:ℝ)^k := by
    have hn : k+2≤2^(k+1) := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k+1))
    have hn' : (k:ℝ)+2≤(2:ℝ)^(k+1) := by exact_mod_cast hn
    simpa only [pow_succ,mul_comm] using hn'
  have hpow : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have hsmall : ‖w c-p‖≤(4+4*A)*(2:ℝ)^k := by
    push_cast at hh
    nlinarith only [hh,hnat,hpow,hA]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(4+4*A)*(2:ℝ)^k)).mpr hsmall
  have hid : ((4+4*A)*(2:ℝ)^k)^2=(4+4*A)^2*(4:ℝ)^k := by
    rw [mul_pow,←pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [hid] at hsq
  have hmul := mul_le_mul_of_nonneg_left hk (sq_nonneg (4+4*A))
  have hid' : (4+4*A)^2*(‖c‖/r+1)=((4+4*A)^2/r)*(‖c‖+r) := by field_simp
  exact hsq.trans (hmul.trans_eq hid')

theorem exact_unit_line_correction_growth {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n) :
    ∃ K r : ℝ,0<K ∧ 0<r ∧ ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,stdDot n a a=1 →
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →∀ c : ℂ,
          ‖affineCorrection u a c-p‖^2≤K*(‖c‖+r) := by
  obtain ⟨D,hD,hres⟩ := exact_line_homotopy_residual_energy_bound hJs hJ hJc hST hT hout
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope hJs hJ hJc hST hT hout
  have hB : 0≤C+M := by linarith
  obtain ⟨r,hr,hlocal⟩ := correction_local_average (n := n) hB hθ.le hθ1
  refine ⟨(4+4*Real.sqrt (128*D))^2/r,r,by positivity,hr,?_⟩
  intro t ht p q u hu a ha hlim c
  have hi := hu.affine_correction_energy_of_slope (lineHomotopy_compact hJc ht) hlim
  have htotal : (∫ z,dirichletEnergy (affineCorrection u a) z)≤D := by
    rw [hi.2]
    exact hres t ht p q u hu
  have he' : ∀ c : ℂ,∀ k : ℕ,
      radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤(C+M)*θ^k := by
    intro c k
    simpa only [ha,mul_one] using he t ht p q u hu a hlim c k
  have hp : affineCorrection u a 0=p := by simpa only [affineCorrection,zero_smul,sub_zero] using hu.2.2.1
  apply scale_growth_squared hr (Real.sqrt_nonneg _) (c := c)
  intro k z hz
  have hh := correction_growth_by_scales (affineCorrection_smooth hu.1 a) hi.1 hD.le htotal hr
    (hlocal u hu.1 he' a ha) k z hz
  rw [hp] at hh
  simpa only [show (2:ℝ)*2=4 by norm_num] using hh


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma stdDot_le_dimension_norm_sq (a : Phase n) : stdDot n a a≤(n:ℝ)*‖a‖^2 := by
  rw [stdDot_apply]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (f := fun i =>
    (a i).re*(a i).re+(a i).im*(a i).im) (g := fun _ => ‖a‖^2) (fun i _ => by
      rw [←Complex.normSq_apply,Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm a i) 2)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

lemma unit_slope_linear_norm {a : Phase n} (ha : stdDot n a a=1) (z : ℂ) :
    ‖z‖^2≤(n:ℝ)*‖z • a‖^2 := by
  have hh := stdDot_le_dimension_norm_sq a
  rw [ha] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖z‖)
  rw [norm_smul,mul_pow]
  nlinarith only [hm]

lemma nonnegative_quadratic_bound {x A B : ℝ} (hx : 0≤x) (hA : 0≤A) (hB : 0≤B)
    (h : x^2≤A+B*x) : x≤A+B+1 := by
  by_contra! hh
  have hxB : B+1<x := by linarith
  have hm := mul_le_mul_of_nonneg_right hxB.le hx
  nlinarith only [h,hm,hh,hB]

lemma sublinear_correction_preimage_bound {u : ℂ → Phase n} {a p : Phase n}
    (ha : stdDot n a a=1) {K r Q : ℝ} (hK : 0≤K) (hr : 0≤r) (hQ : 0≤Q)
    (hg : ∀ c : ℂ,‖affineCorrection u a c-p‖^2≤K*(‖c‖+r))
    {c : ℂ} (hc : ‖u c‖≤Q) :
    ‖c‖≤2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r+2*(n:ℝ)*K+1 := by
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hlin := unit_slope_linear_norm ha c
  have hcor := hg c
  have htri1 := norm_le_norm_add_norm_sub (u c) (c • a)
  change ‖c • a‖≤‖u c‖+‖affineCorrection u a c‖ at htri1
  have htri2 := norm_le_norm_add_norm_sub p (affineCorrection u a c)
  rw [norm_sub_rev p] at htri2
  have hnlin : ‖c • a‖≤Q+‖p‖+‖affineCorrection u a c-p‖ := by linarith
  have hs : ‖c • a‖^2≤2*(Q+‖p‖)^2+2*‖affineCorrection u a c-p‖^2 := by
    have hs' := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Q+‖p‖+‖affineCorrection u a c-p‖)).mpr hnlin
    nlinarith [sq_nonneg ((Q+‖p‖)-‖affineCorrection u a c-p‖)]
  have hh := hlin.trans (mul_le_mul_of_nonneg_left hs hn)
  have hm := mul_le_mul_of_nonneg_left hcor (by positivity : 0≤2*(n:ℝ))
  have hquad : ‖c‖^2≤(2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r)+(2*(n:ℝ)*K)*‖c‖ := by
    nlinarith only [hh,hm]
  exact nonnegative_quadratic_bound (norm_nonneg _) (by positivity) (by positivity) hquad

theorem exact_unit_line_source_escape {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n) (p : Phase n) {Q : ℝ} (hQ : 0≤Q) :
    ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ a : Phase n,stdDot n a a=1 →
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →∀ c : ℂ,
      ‖u c‖≤Q →‖c‖≤R := by
  obtain ⟨K,r,hK,hr,hg⟩ := exact_unit_line_correction_growth hJs hJ hJc hST hT hout
  refine ⟨2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r+2*(n:ℝ)*K+1,by positivity,?_⟩
  intro t ht q u hu a ha hlim c hc
  exact sublinear_correction_preimage_bound ha hK.le hr.le hQ (hg t ht p q u hu a ha hlim) hc


lemma dilatedCurve_original_second_mark {J : Phase n → End n} {p q : Phase n}
    {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) {a : Phase n} (ha : a≠0) :
    dilatedCurve u (slopeScale a) (Real.sqrt (stdDot n a a))=q := by
  change u ((slopeScale a : ℂ)*(Real.sqrt (stdDot n a a) : ℂ))=q
  rw [←Complex.ofReal_mul]
  have hid : slopeScale a*Real.sqrt (stdDot n a a)=1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (stdDot_pos ha)).ne'
  rw [hid,Complex.ofReal_one]
  exact hu.2.2.2.1

theorem exact_line_slope_lower_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) :
    ∃ d : ℝ,0<d ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,a≠0 →Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        d≤ stdDot n a a := by
  obtain ⟨B,θ,hB,hθ,hθ1,he⟩ := exact_normalized_line_energy hJs hJ hJc hST hT hout
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB.le hθ.le hθ1 (dist_pos.mpr hpq)
  refine ⟨δ^2,sq_pos_of_pos hδ,?_⟩
  intro t ht u hu a ha hlim
  have hlower : δ≤Real.sqrt (stdDot n a a) := by
    by_contra! h
    have hc : dist (0:ℂ) (Real.sqrt (stdDot n a a) : ℂ)<δ := by
      simpa only [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using h
    have hh := hmod (dilatedCurve u (slopeScale a)) (dilatedCurve_smooth hu.1 _)
      (he t ht p q u hu a ha hlim) 0 (Real.sqrt (stdDot n a a)) hc
    rw [dilatedCurve_original_second_mark hu ha] at hh
    have hz : dilatedCurve u (slopeScale a) 0=p := by simpa only [dilatedCurve,mul_zero] using hu.2.2.1
    rw [hz] at hh
    exact lt_irrefl _ hh
  nlinarith [Real.sq_sqrt (stdDot_nonneg a),Real.sqrt_nonneg (stdDot n a a)]


theorem exact_line_slope_upper_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ D : ℝ,0<D ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,a≠0 →Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        stdDot n a a≤D := by
  obtain ⟨R,hR,hesc⟩ := exact_unit_line_source_escape hJs hJ hJc hST hT hout p (norm_nonneg q)
  refine ⟨R^2,sq_pos_of_pos hR,?_⟩
  intro t ht u hu a ha hlim
  have hs : (slopeScale a : ℂ)≠0 := by exact_mod_cast (slopeScale_pos ha).ne'
  have hlu := dilatedCurve_slope hlim hs
  have hnorm : stdDot n ((slopeScale a : ℂ) • a) ((slopeScale a : ℂ) • a)=1 := by
    simpa only [Complex.coe_smul] using normalizedSlope_unit ha
  have hh := hesc t ht (u (slopeScale a)) (dilatedCurve u (slopeScale a)) (hu.dilate hs)
    ((slopeScale a : ℂ) • a) hnorm hlu (Real.sqrt (stdDot n a a)) (by
      rw [dilatedCurve_original_second_mark hu ha])
  have hb : Real.sqrt (stdDot n a a)≤R := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hh
  nlinarith [Real.sq_sqrt (stdDot_nonneg a),Real.sqrt_nonneg (stdDot n a a)]

theorem exact_marked_line_slope_bounds {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    (p q : Phase n) (hpq : p≠q) :
    ∃ d D : ℝ,0<d ∧ 0<D ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,a≠0 →Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        d≤ stdDot n a a ∧ stdDot n a a≤D := by
  obtain ⟨d,hd,hlo⟩ := exact_line_slope_lower_bound hJs hJ hJc hST hT hout hpq
  obtain ⟨D,hD,hup⟩ := exact_line_slope_upper_bound hJs hJ hJc hST hT hout p q
  exact ⟨d,D,hd,hD,fun t ht u hu a ha hlim => ⟨hlo t ht u hu a ha hlim,hup t ht u hu a ha hlim⟩⟩


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {ι : Type*}

lemma anchored_uniform_point_bound {F : ι → ℂ → Phase n} {p : Phase n}
    (hp : ∀ i,F i 0=p) {δ : ℝ} (hδ : 0<δ)
    (hF : ∀ i,∀ z w : ℂ,dist z w<δ →dist (F i z) (F i w)≤1) (x : ℂ) :
    ∃ M : ℝ,∀ i,‖F i x‖≤M := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (‖x‖/δ) 0)
  have hNp : 0<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hstep : ‖x‖/(N:ℝ)<δ := (div_lt_iff₀ hNp).mpr (by
    have hh := lt_of_le_of_lt (le_max_left _ _) hN
    have hh' := (div_lt_iff₀ hδ).mp hh
    nlinarith)
  let path : ℕ → ℂ := fun k => ((k:ℝ)/(N:ℝ)) • x
  have hp0 : path 0=0 := by simp [path]
  have hpN : path N=x := by
    change ((N:ℝ)/(N:ℝ)) • x=x
    rw [div_self hNp.ne',one_smul]
  have hdiff (k : ℕ) : path (k+1)-path k=((1:ℝ)/(N:ℝ)) • x := by
    dsimp only [path]
    rw [←sub_smul]
    congr 1
    push_cast
    ring
  have hpath (k : ℕ) : dist (path k) (path (k+1))<δ := by
    rw [dist_comm,dist_eq_norm,hdiff,norm_smul,Real.norm_of_nonneg (by positivity)]
    convert hstep using 1
    ring
  refine ⟨‖p‖+(N:ℝ),?_⟩
  intro i
  have hh := dist_le_range_sum_of_dist_le (f := fun k => F i (path k)) N (d := fun _ => (1:ℝ))
    (fun {k} _ => hF i (path k) (path (k+1)) (hpath k))
  simp only [hp0,hpN,hp,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hh
  have htri := dist_triangle (0:Phase n) p (F i x)
  simp only [dist_zero_left] at htri
  linarith

lemma energy_family_point_bound {F : ι → ℂ → Phase n} {p : Phase n}
    (hp : ∀ i,F i 0=p) (hs : ∀ i,ContDiff ℝ ∞ (F i))
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ i,∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve (F i) c) ((1/16)^k)≤B*θ^k)
    (x : ℂ) : ∃ M : ℝ,∀ i,‖F i x‖≤M := by
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 (by norm_num : (0:ℝ)<1)
  exact anchored_uniform_point_bound hp hδ (fun i z w hzw => (hmod (F i) (hs i) (he i) z w hzw).le) x



end HigherDimensionalBallPacking.Rigidity
end

end OAI
