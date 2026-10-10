import Mathlib
import OAI.Probability.SKSupport.Foundations.DerivVarianceHeatCurve

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma backward_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |backward c b f r z-backward c b f s y| ≤ (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ := (backward_verificationData hf hLip hc b).bounds
  have ht (z : ℝ) : LipschitzOnWith Ct (fun r => backward c b f r z) (Set.Icc 0 b) := by
    apply (convex_Icc (0:ℝ) b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun r hr => hd r hr z)
    intro r hr
    exact NNReal.coe_le_coe.mp (by simpa only [coe_nnnorm,Real.norm_eq_abs] using hCt r z)
  refine ⟨Ct+1, fun r hr s hs z y => ?_⟩
  have htime := (ht z).dist_le_mul r hr s hs
  have hspace := (varianceLogHeat_lipschitz hLip hc (b-s)).dist_le_mul z y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at htime hspace
  change |backward c b f s z-backward c b f s y| ≤ |z-y| at hspace
  have htri := abs_sub_le (backward c b f r z) (backward c b f s z) (backward c b f s y)
  simp only [NNReal.coe_add, NNReal.coe_one]
  nlinarith [abs_nonneg (r-s),mul_nonneg Ct.coe_nonneg (abs_nonneg (z-y))]

lemma deriv_varianceLogHeat_tilted {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    deriv (varianceLogHeat c t f) = varianceTilted c t f (deriv f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  funext x
  rw [varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable
    hf.deriv_bounded.smooth.continuous.measurable]
  by_cases hc0 : c = 0
  · subst c
    have hz : logSemigroup 0 (Real.toNNReal t) f = semigroup (Real.toNNReal t) f := by
      funext z; simp [logSemigroup]
    rw [hz,(hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip (Real.toNNReal t) x).deriv]
    simp [tiltedMean,semigroup]
  · exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip
      (lt_of_le_of_ne hc (Ne.symm hc0)) (Real.toNNReal t) x).deriv

lemma backward_gradient_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |deriv (backward c b f r) z-deriv (backward c b f s) y| ≤ (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hf.deriv_bounded hc
  refine ⟨L, fun r hr s hs z y => ?_⟩
  rw [show backward c b f r = varianceLogHeat c (b-r) f from rfl,
    show backward c b f s = varianceLogHeat c (b-s) f from rfl,
    deriv_varianceLogHeat_tilted hf hLip hc, deriv_varianceLogHeat_tilted hf hLip hc]
  have hb := hL (b-r) (sub_nonneg.mpr hr.2) (b-s) (sub_nonneg.mpr hs.2) z y
  have he : |(b-r)-(b-s)| = |r-s| := by rw [show (b-r)-(b-s) = -(r-s) by ring,abs_neg]
  rwa [he] at hb

lemma continuousOn_of_joint_bound {F : ℝ → ℝ → ℝ} {L : ℝ≥0} {a b : ℝ}
    (hL : ∀ r ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ z y,
      |F r z-F s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ) := by
  have hl : LipschitzOnWith (2*L) (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    have hh := hL p.1 hp.1 q.1 hq.1 p.2 q.2
    rw [Real.dist_eq]
    have ht : |p.1-q.1| ≤ dist p q := by
      change dist p.1 q.1 ≤ max (dist p.1 q.1) (dist p.2 q.2)
      exact le_max_left _ _
    have hx : |p.2-q.2| ≤ dist p q := by
      change dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2)
      exact le_max_right _ _
    simp only [NNReal.coe_mul,NNReal.coe_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add ht hx) L.coe_nonneg]
  exact hl.continuousOn

lemma continuousOn_moving_heat {F : ℝ → ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hm : ∀ r, Measurable (F r))
    (hL : ∀ r ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ z y,
      |F r z-F s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) (x : ℝ) :
    ContinuousOn (fun r => varianceHeat (r-a) (F r) x) (Set.Icc a b) := by
  apply continuousOn_of_dominated
    (bound := fun y : ℝ => |F a x|+(L:ℝ)*((b-a)+Real.sqrt (b-a)*|y|))
  · intro r hr
    exact ((hm r).comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  · intro r hr
    filter_upwards [] with y
    have hh := hL r hr a ⟨le_rfl,hab⟩ (x+Real.sqrt (r-a)*y) x
    have ht := abs_add_le (F r (x+Real.sqrt (r-a)*y)-F a x) (F a x)
    rw [sub_add_cancel] at ht
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hh
    have hs : Real.sqrt (r-a) ≤ Real.sqrt (b-a) := Real.sqrt_le_sqrt (by linarith [hr.2])
    rw [Real.norm_eq_abs]
    change |F r (x+Real.sqrt (r-a)*y)| ≤ _
    have hmrs := mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    have hh' := mul_le_mul_of_nonneg_left (add_le_add (show r-a ≤ b-a by linarith [hr.2]) hmrs) L.coe_nonneg
    linarith
  · exact (integrable_const _).add
      (((integrable_const _).add (integrable_standardGaussian_abs.const_mul _)).const_mul _)
  · filter_upwards [] with y
    exact (continuousOn_of_joint_bound hL).comp
      ((continuous_id.prodMk (continuous_const.add ((Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const)).mul continuous_const))).continuousOn)
      (fun r hr => ⟨hr,Set.mem_univ _⟩)

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_backward_curve {f X : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c b : ℝ) {s X' : ℝ}
    (hX : HasDerivAt X X' s) (hs : s < b) :
    HasDerivAt (fun r => backward c b f r (X r))
      (-(1/2:ℝ)*deriv (deriv (backward c b f s)) (X s)-
        c/2*(deriv (backward c b f s) (X s))^2+
        X'*deriv (backward c b f s) (X s)) s := by
  have hd := hasDerivAt_varianceLogHeat_curve hf hLip c
    ((hasDerivAt_const s b).sub (hasDerivAt_id s)) hX (sub_pos.mpr hs)
  simp only [Pi.sub_apply,id_eq] at hd
  rw [show backward c b f s = varianceLogHeat c (b-s) f from rfl]
  convert hd using 1 <;> first | rfl | ring

lemma hasDerivAt_moving_backward_heat {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {a b s : ℝ}
    (has : a < s) (hsb : s < b) (x : ℝ) :
    HasDerivAt (fun r => varianceHeat (r-a) (backward c b f r) x)
      (-(c/2)*varianceHeat (s-a) (fun z => (deriv (backward c b f s) z)^2) x) s := by
  let U : ℝ → ℝ → ℝ := fun r => deriv (backward c b f r)
  let W : ℝ → ℝ → ℝ := fun r => deriv (deriv (backward c b f r))
  let D : ℝ → ℝ → ℝ := fun r y =>
    -(1/2:ℝ)*W r (x+Real.sqrt (r-a)*y)-c/2*(U r (x+Real.sqrt (r-a)*y))^2+
      (y/(2*Real.sqrt (r-a)))*U r (x+Real.sqrt (r-a)*y)
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hdt,hJ,hE⟩ := (backward_verificationData hf hLip hc b).bounds
  have hub (r z : ℝ) : |U r z| ≤ 1 := (backward_verificationData hf hLip hc b).gradient_bound r z
  have hwb (r z : ℝ) : |W r z| ≤ C₂ := h₂ r z
  have hreg (r : ℝ) : RegularDatum (backward c b f r) := regularDatum_varianceLogHeat hf hLip hc (b-r)
  have hUmeas (r : ℝ) : Measurable (U r) := (hreg r).deriv_bounded.smooth.continuous.measurable
  have hWmeas (r : ℝ) : Measurable (W r) := (hreg r).deriv_bounded.deriv.smooth.continuous.measurable
  have hsmall : 0 < (s-a)/2 := by linarith
  have hroot : 0 < Real.sqrt ((s-a)/2) := Real.sqrt_pos.mpr hsmall
  have hiF : Integrable (fun y => backward c b f s (x+Real.sqrt (s-a)*y)) (gaussianReal 0 1) :=
    integrable_scaled_of_expBound (hreg s).smooth.continuous.measurable
      (exponentialBound_of_lipschitz (varianceLogHeat_lipschitz hLip hc (b-s))) _ _
  have hDm : AEStronglyMeasurable (D s) (gaussianReal 0 1) := by
    dsimp only [D]
    exact (((measurable_const.mul ((hWmeas s).comp (by fun_prop))).sub
      (measurable_const.mul (((hUmeas s).comp (by fun_prop)).pow_const 2))).add
      ((measurable_id.div_const _).mul ((hUmeas s).comp (by fun_prop)))).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r y => backward c b f r (x+Real.sqrt (r-a)*y)) (F' := D)
    (bound := fun y : ℝ => ((C₂:ℝ)+c)/2+|y|/(2*Real.sqrt ((s-a)/2)))
    (s := Set.Ioo ((a+s)/2) b) (Ioo_mem_nhds (by linarith) hsb)
    (Filter.Eventually.of_forall (fun r => ((hreg r).smooth.continuous.measurable.comp
      (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable))
    hiF hDm
    (by
      filter_upwards [] with y r hr
      have hra : 0 < r-a := by linarith [hr.1]
      have hsr : Real.sqrt ((s-a)/2) ≤ Real.sqrt (r-a) := Real.sqrt_le_sqrt (by linarith [hr.1])
      have hratio : |y|/(2*Real.sqrt (r-a)) ≤ |y|/(2*Real.sqrt ((s-a)/2)) := by
        exact div_le_div_of_nonneg_left (abs_nonneg y) (by positivity) (by linarith)
      dsimp only [D]
      rw [Real.norm_eq_abs]
      apply (abs_add_le _ _).trans
      apply (add_le_add (abs_sub _ _) le_rfl).trans
      have hU := hub r (x+Real.sqrt (r-a)*y)
      have hW := hwb r (x+Real.sqrt (r-a)*y)
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2), abs_mul,
        abs_of_nonneg (div_nonneg hc (by norm_num)), abs_pow,
        abs_mul, abs_div, abs_of_pos (show 0 < 2*Real.sqrt (r-a) by positivity)]
      have hU2 : |U r (x+Real.sqrt (r-a)*y)|^2 ≤ 1 := by nlinarith [abs_nonneg (U r (x+Real.sqrt (r-a)*y))]
      have hUterm := mul_le_mul_of_nonneg_left hU (show 0 ≤ |y|/(2*Real.sqrt (r-a)) by positivity)
      have hU2term := mul_le_mul_of_nonneg_left hU2 (div_nonneg hc (by norm_num : (0:ℝ)≤2))
      nlinarith)
    ((integrable_const _).add (integrable_standardGaussian_abs.div_const _))
    (by
      filter_upwards [] with y r hr
      have hra : 0 < r-a := by linarith [hr.1]
      have hX : HasDerivAt (fun t : ℝ => x+Real.sqrt (t-a)*y)
          (y/(2*Real.sqrt (r-a))) r := by
        convert ((((hasDerivAt_id r).sub_const a).sqrt (ne_of_gt hra)).mul_const y).const_add x using 1 <;> first | rfl | (simp only [id_eq]; ring)
      exact hasDerivAt_backward_curve hf hLip c b hX hr.2)
  have hUc : BoundedSmooth (U s) := (hreg s).deriv_bounded
  have hUe : ExponentialBound (U s) := ExponentialBound.of_bounded (A := 1) (hub s)
  have hWe : ExponentialBound (W s) := ExponentialBound.of_bounded (hwb s)
  have hUi := integrable_mul_scaled_of_expBound (hUmeas s) hUe (Real.sqrt (s-a)) x
  have hWi := integrable_scaled_of_expBound (hWmeas s) hWe (Real.sqrt (s-a)) x
  have hU2m : Measurable (fun z => (U s z)^2) := (hUmeas s).pow_const 2
  have hU2e : ExponentialBound (fun z => (U s z)^2) := ExponentialBound.of_bounded (A := 1) (fun z => by
    rw [abs_pow]; norm_num only [NNReal.coe_one]; nlinarith [hub s z,abs_nonneg (U s z)])
  have hU2i := integrable_scaled_of_expBound hU2m hU2e (Real.sqrt (s-a)) x
  have hstein := scaled_gradient_stein hUc (Real.sqrt (s-a)) x
  rw [(hasDerivAt_scaled_space (hUc.smooth.of_le (by simp)) hUe hWe (Real.sqrt (s-a)) x).deriv] at hstein
  have heD : D s = fun y => -(1/2:ℝ)*W s (x+Real.sqrt (s-a)*y)-
      c/2*(U s (x+Real.sqrt (s-a)*y))^2+
      (1/(2*Real.sqrt (s-a)))*(y*U s (x+Real.sqrt (s-a)*y)) := by
    funext y; dsimp only [D]; ring
  have he : (∫ y,D s y ∂gaussianReal 0 1) =
      -(c/2)*varianceHeat (s-a) (fun z => (U s z)^2) x := by
    rw [heD]
    dsimp only
    have hsplit := integral_add ((hWi.const_mul (-(1/2:ℝ))).sub (hU2i.const_mul (c/2))) (hUi.const_mul (1/(2*Real.sqrt (s-a))))
    have hsub := integral_sub (hWi.const_mul (-(1/2:ℝ))) (hU2i.const_mul (c/2))
    simp only [Pi.sub_apply] at hsplit hsub
    rw [hsplit,hsub,integral_const_mul,integral_const_mul,integral_const_mul,← hstein]
    change -(1/2:ℝ)*scaled (Real.sqrt (s-a)) (W s) x-c/2*scaled (Real.sqrt (s-a)) (fun z => (U s z)^2) x+
      (1/(2*Real.sqrt (s-a)))*(Real.sqrt (s-a)*scaled (Real.sqrt (s-a)) (W s) x) = _
    dsimp only [varianceHeat]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr has))]
    ring
  exact hd.2.congr_deriv he

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
