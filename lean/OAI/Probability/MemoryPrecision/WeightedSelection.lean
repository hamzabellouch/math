import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.MeasurableTests

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def realNormalize {d : ℕ} (ν : Measure (Space d)) (β H : ℝ) (z : Space d) (r : ℝ) :
    Measure (Space d) :=
  (ENNReal.ofReal (H * r^β))⁻¹ •
    (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

lemma realNormalize_local {d : ℕ} {ν : Measure (Space d)} {β H : ℝ}
    (hν : AmbientBallBound ν H β) (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    AmbientBallBound (realNormalize ν β H z r) 1 β := by
  have hc0 : ENNReal.ofReal (H*r^β) ≠ 0 := by positivity
  intro t ρ hρ
  rw [realNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : Space d => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x-(z+r•t) = r • (r⁻¹ • (x-z)-t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (ENNReal.ofReal (H*r^β))⁻¹ * ν (Metric.closedBall (z+r•t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (ENNReal.ofReal (H*r^β))⁻¹ * ENNReal.ofReal (H*(r*ρ)^β) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (1*ρ^β) := by
      rw [Real.mul_rpow hr.le hρ.le, ← mul_assoc,
        ENNReal.ofReal_mul (by positivity : 0 ≤ H*r^β), ← mul_assoc,
        ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul, one_mul]

lemma realNormalize_support {d : ℕ} (ν : Measure (Space d)) (β H : ℝ)
    (z : Space d) {r : ℝ} (hr : 0 < r) :
    (realNormalize ν β H z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, realNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : Space d => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : Space d => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩
      Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

lemma realNormalize_finite {d : ℕ} (ν : Measure (Space d)) [IsFiniteMeasure ν]
    {β H : ℝ} (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (realNormalize ν β H z r) := by
  constructor
  rw [realNormalize, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (by positivity)
  · exact measure_lt_top _ _

lemma realNormalize_reconstruct {d : ℕ} (ν : Measure (Space d)) {β H : ℝ}
    (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (H*r^β) • (realNormalize ν β H z r).map (fun t => z+r•t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : ENNReal.ofReal (H*r^β) ≠ 0 := by positivity
  rw [realNormalize, Measure.map_smul _ (by fun_prop), smul_smul,
    ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_smul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : Space d => z+r•t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma normalized_scale_le {d m p : ℕ} (hp : 2 ≤ p) {β K : ℝ} (hK : 1 ≤ K)
    (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d) :
    ProjectionNormScale m p 1 β 1 ≤ K^d := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hprod0 : 0 ≤ ∏ j ∈ Finset.range (p-1), J β m j := by
    apply Finset.prod_nonneg
    intro j hj
    apply (J_pos ?_).le
    have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by have := Finset.mem_range.mp hj; omega)
    linarith
  have hprod : (∏ j ∈ Finset.range (p-1), J β m j) ≤ (K^d)^(p-1) := by
    calc
      _ ≤ ∏ _j ∈ Finset.range (p-1), K^d := by
        apply Finset.prod_le_prod₀
        · intro j hj
          apply (J_pos ?_).le
          have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by have := Finset.mem_range.mp hj; omega)
          linarith
        · intro j hj
          exact hJ j (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by simp
  have hpeak : (2*Real.pi) ^ (-(m:ℝ)*((p:ℝ)-1)/(2*(p:ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · linarith [Real.pi_gt_three]
    · have : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (by linarith)
      · positivity
  unfold ProjectionNormScale
  simp only [mul_one, Real.one_rpow]
  calc
    _ ≤ 1 * (∏ j ∈ Finset.range (p-1), J β m j)^(1/(p:ℝ)) :=
      mul_le_mul_of_nonneg_right hpeak (Real.rpow_nonneg hprod0 _)
    _ ≤ ((K^d)^(p-1))^(1/(p:ℝ)) := by rw [one_mul]; exact Real.rpow_le_rpow hprod0 hprod (by positivity)
    _ = (K^d)^(((p-1:ℕ):ℝ)/(p:ℝ)) := by
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ K^d)]
      congr 1
      ring
    _ ≤ (K^d)^(1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hK)
      rw [div_le_one hp0]
      exact_mod_cast Nat.sub_le p 1
    _ = _ := Real.rpow_one _

lemma normalized_weighted_selection {d m p N : ℕ} (ν : Fin N → Measure (Space d))
    [∀ w, IsFiniteMeasure (ν w)] (hp : 2 ≤ p) (hm : 1 ≤ m) (hmd : m ≤ d)
    {β K : ℝ} (hK : 1 ≤ K) (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d)
    (hball : ∀ w, AmbientBallBound (ν w) 1 β)
    (hsupport : ∀ w, (ν w).support ⊆ Metric.closedBall 0 1)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (hg : ∀ w, Measurable (g w)) (hgsum : ∀ x, ∑ w, g w x ≤ 1) :
    (∑ w, ∫⁻ x, g w x ∂projectionLaw (ν w) m) ≤
      ENNReal.ofReal (K*192)^d * (N:ℝ≥0∞)^(1/(p:ℝ)) := by
  classical
  obtain ⟨D,hD,hDs,hDV⟩ := exists_projection_support (E := Space d) m (by simpa using hmd)
  have hg1 (w) (x) : g w x ≤ 1 :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ w)).trans (hgsum x)
  have hpoint (w) : (∫⁻ x, g w x ∂projectionLaw (ν w) m) ≤
      ENNReal.ofReal (K^d) * (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) := by
    obtain ⟨F,hF,hF0,hden,_,hnorm⟩ := exact_finite_density d m p hp hm β 1 1 hgap
      (by norm_num) (by norm_num) 0 (ν w) (hsupport w) (hball w)
    have hFD : ∀ᵐ x ∂matrixLabelReference m, x ∉ D → F x = 0 := by
      have hz : projectionLaw (ν w) m Dᶜ = 0 := by
        rw [← compl_mem_ae_iff, compl_compl]
        unfold projectionLaw
        apply (ae_map_iff (by fun_prop) hD).2
        filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν w).support_mem_ae] with x hx
        exact hDs x.1 x.2 (by simpa using hsupport w hx)
      change (matrixLabelReference m).withDensity _ = projectionLaw (ν w) m at hden
      rw [← hden, withDensity_apply _ hD.compl] at hz
      have ha := (lintegral_eq_zero_iff' hF.ennreal_ofReal.aemeasurable).mp hz
      change ∀ᵐ x ∂(matrixLabelReference m).restrict Dᶜ, ENNReal.ofReal (F x) = 0 at ha
      rw [ae_restrict_iff' hD.compl] at ha
      filter_upwards [ha] with x hx hnot
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp (hx hnot)) (hF0 x)
    have hn : eLpNorm F (p:ℝ≥0∞) (matrixLabelReference m) ≤ ENNReal.ofReal (K^d) :=
      hnorm.trans (ENNReal.ofReal_le_ofReal (normalized_scale_le hp hK hgap hJ))
    have ht := density_test_bound (matrixLabelReference m) F hF hF0 p hp
      (ENNReal.ofReal (K^d)) hn D hD hFD (g w) (hg w).aemeasurable (hg1 w)
    change (matrixLabelReference m).withDensity _ = projectionLaw (ν w) m at hden
    rwa [hden] at ht
  have hq0 : 0 ≤ 1-1/(p:ℝ) := by
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp1]
  have hsum : (∑ w, ∫⁻ x in D, g w x ∂matrixLabelReference m) ≤
      matrixLabelReference (E := Space d) m D := by
    rw [← lintegral_finsetSum _ (fun w _ => hg w)]
    simpa using lintegral_mono (μ := (matrixLabelReference (E := Space d) m).restrict D) hgsum
  have hv : (matrixLabelReference (E := Space d) m D)^(1-1/(p:ℝ)) ≤ (192:ℝ≥0∞)^d := by
    calc
      _ ≤ ((192:ℝ≥0∞)^d)^(1-1/(p:ℝ)) := ENNReal.rpow_le_rpow (by simpa using hDV) hq0
      _ ≤ ((192:ℝ≥0∞)^d)^(1:ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ ≤ ∑ w, ENNReal.ofReal (K^d) * (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) :=
      Finset.sum_le_sum (fun w _ => hpoint w)
    _ = ENNReal.ofReal (K^d) * ∑ w, (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (K^d) * ((N:ℝ≥0∞)^(1/(p:ℝ)) *
        (∑ w, ∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ))) := by
      apply mul_le_mul' le_rfl
      simpa using finite_rpow_holder (fun w => ∫⁻ x in D, g w x ∂matrixLabelReference m)
        (by exact_mod_cast (by omega : 1 < p))
    _ ≤ ENNReal.ofReal (K^d) * ((N:ℝ≥0∞)^(1/(p:ℝ)) * (192:ℝ≥0∞)^d) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl ((ENNReal.rpow_le_rpow hsum hq0).trans hv))
    _ = _ := by
      rw [ENNReal.ofReal_pow (by linarith : 0 ≤ K), mul_left_comm, ← mul_pow,
        ENNReal.ofReal_mul (by linarith : 0 ≤ K)]
      norm_num
      ring
lemma localized_weighted_selection {d m p N : ℕ} (ν : Fin N → Measure (Space d))
    [∀ w, IsFiniteMeasure (ν w)] (hp : 2 ≤ p) (hm : 1 ≤ m) (hmd : m ≤ d)
    {β K H : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d)
    (hball : ∀ w, AmbientBallBound (ν w) H β)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (hg : ∀ w, Measurable (g w)) (hgsum : ∀ x, ∑ w, g w x ≤ 1)
    (z : Space d) {r : ℝ} (hr : 0 < r) :
    (∑ w, ∫⁻ x, g w x ∂projectionLaw ((ν w).restrict (Metric.closedBall z r)) m) ≤
      ENNReal.ofReal ((K*192)^d * (N:ℝ)^(1/(p:ℝ)) * H * r^β) := by
  let τ w := realNormalize (ν w) β H z r
  let (w : Fin N) : IsFiniteMeasure (τ w) := realNormalize_finite (ν w) hH z hr
  let F : ((Fin m → Space d) × (Fin m → ℝ)) → ((Fin m → Space d) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r*x.2 i)
  have hF : Measurable F := by fun_prop
  have hb := normalized_weighted_selection τ hp hm hmd hK hgap hJ
    (fun w => realNormalize_local (hball w) hH z hr)
    (fun w => realNormalize_support (ν w) β H z hr)
    (fun w => g w ∘ F) (fun w => (hg w).comp hF) (fun x => hgsum (F x))
  have he (w) : (∫⁻ x, g w x ∂projectionLaw ((ν w).restrict (Metric.closedBall z r)) m) =
      ENNReal.ofReal (H*r^β) * ∫⁻ x, g w (F x) ∂projectionLaw (τ w) m := by
    rw [← realNormalize_reconstruct (ν w) (β := β) hH z hr, projectionLaw_smul,
      projectionLaw_affine, lintegral_smul_measure, smul_eq_mul, lintegral_map (hg w) hF]
  simp_rw [he]
  rw [← Finset.mul_sum]
  refine (mul_le_mul' le_rfl hb).trans_eq ?_
  rw [← ENNReal.ofReal_natCast N, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ K*192),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (K*192)^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ H*r^β)]
  congr 1
  ring

end MemoryPrecision


end

end OAI
