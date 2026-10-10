import Mathlib
import OAI.Probability.GaussianRegression.Main

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v



open MeasureTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def J (β : ℝ) (m j : ℕ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  1 + three^j * two^β * (m : ℝ) / (β - (j : ℝ) - (m : ℝ))

def AmbientBallBound {d : ℕ} (μ : Measure (Space d)) (H β : ℝ) : Prop :=
  ∀ x : Space d, ∀ r : ℝ, 0 < r →
    μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H * r^β)

def InverseGram {d p : ℕ} (m : ℕ) (v : Space d × (Fin (p-1) → Space d)) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
  letI : Inner ℝ (Space d) := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ (fun i => v.2 i - v.1)).det)⁻¹ ^ m)

lemma sharp_inverse_unit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {m a C : ℝ} (hm : 0 < m) (ha : m < a) (hC : 0 ≤ C)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ t} ≤ ENNReal.ofReal (C * t^a)) :
    (∫⁻ x, ENNReal.ofReal (f x ^ (-m)) ∂μ) ≤
      μ univ + ENNReal.ofReal (C * m / (a-m)) := by
  have htail (t : ℝ) (ht : 1 < t) :
      μ {x | t < f x ^ (-m)} ≤ ENNReal.ofReal (C * t ^ (-a/m)) := by
    have ht0 : 0 < t := by linarith
    have hr0 : 0 < t ^ ((-m)⁻¹) := Real.rpow_pos_of_pos ht0 _
    have hr1 : t ^ ((-m)⁻¹) ≤ 1 := by
      calc
        _ ≤ t ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht.le (inv_nonpos.mpr (by linarith))
        _ = 1 := Real.rpow_zero _
    have hsub : {x | t < f x ^ (-m)} ⊆ {x | f x ≤ t ^ ((-m)⁻¹)} := by
      intro x hx
      have hfx : 0 < f x := by
        by_contra h
        have heq : f x = 0 := le_antisymm (le_of_not_gt h) (hf0 x)
        simp only [mem_ofPred_eq, heq, Real.zero_rpow (neg_ne_zero.mpr hm.ne')] at hx
        linarith
      exact ((Real.lt_rpow_inv_iff_of_neg hfx ht0 (by linarith)).2 hx).le
    calc
      _ ≤ μ {x | f x ≤ t ^ ((-m)⁻¹)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (t ^ ((-m)⁻¹)) ^ a) := htube _ hr0 hr1
      _ = _ := by
        rw [← Real.rpow_mul ht0.le]
        congr 2
        ring_nf
  have hb : -a/m < -1 := by
    rw [div_lt_iff₀ hm]
    linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-a/m)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hb (by norm_num)).const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1:ℝ))] (fun t : ℝ => C * t ^ (-a/m)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact mul_nonneg hC (Real.rpow_nonneg (by have ht' : (1:ℝ) < t := ht; linarith : 0 ≤ t) _)
  have htailint : (∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (C * t ^ (-a/m))) =
      ENNReal.ofReal (C * m / (a-m)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_Ioi_rpow_of_lt hb (by norm_num), Real.one_rpow]
    congr 1
    field_simp [hm.ne', show a - m ≠ 0 by linarith, show -a + m ≠ 0 by linarith]
    ring
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht,_⟩ | ht) <;> linarith
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hf0 x) _) (hf.pow_const _).aemeasurable,
    hsplit]
  apply (lintegral_union_le _ _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _t in Ioc (0:ℝ) 1, μ univ := lintegral_mono fun t => measure_mono (subset_univ _)
      _ = μ univ := by simp [Real.volume_Ioc]
  · calc
      _ ≤ ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (C * t ^ (-a/m)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
        exact htail t ht
      _ = _ := htailint

lemma ae_pos_of_power_tube {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {a C : ℝ} (ha : 0 < a)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ t} ≤ ENNReal.ofReal (C * t^a)) : ∀ᵐ x ∂μ, 0 < f x := by
  have hb (n : ℕ) : μ {x | f x ≤ 0} ≤ ENNReal.ofReal (C * ((1/2 : ℝ)^n)^a) := by
    calc
      μ {x | f x ≤ 0} ≤ μ {x | f x ≤ (1/2 : ℝ)^n} :=
        measure_mono fun x hx => (show f x ≤ 0 from hx).trans (by positivity)
      _ ≤ _ := htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * ((1/2 : ℝ)^n)^a)) atTop (𝓝 (0:ℝ≥0∞)) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).rpow_const_nhds_zero ha
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul h)
  have hz := le_antisymm (ge_of_tendsto' hlim hb) (bot_le : (0:ℝ≥0∞) ≤ μ {x | f x ≤ 0})
  simpa only [ae_iff, not_lt] using hz

lemma sharp_inverse_scaled {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {m a B C R : ℝ} (hm : 0 < m) (ha : m < a)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 0 < R)
    (hmass : μ univ ≤ ENNReal.ofReal B)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ R*t} ≤ ENNReal.ofReal (C * t^a)) :
    (∀ᵐ x ∂μ, 0 < f x) ∧
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (-m) ∂μ) ≤
      ENNReal.ofReal ((B + C*m/(a-m)) * R^(-m)) := by
  have hg0 (x : X) : 0 ≤ f x / R := div_nonneg (hf0 x) hR.le
  have hg : Measurable (fun x => f x / R) := hf.div_const R
  have hgtube (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      μ {x | f x / R ≤ t} ≤ ENNReal.ofReal (C*t^a) := by
    have heq : {x | f x / R ≤ t} = {x | f x ≤ R*t} := by
      ext x
      simp only [mem_ofPred_eq, div_le_iff₀ hR, mul_comm]
    rw [heq]
    exact htube t ht ht1
  have hgp := ae_pos_of_power_tube μ (fun x => f x / R) (hm.trans ha) hgtube
  have hfp : ∀ᵐ x ∂μ, 0 < f x := by
    filter_upwards [hgp] with x hx
    exact (div_pos_iff_of_pos_right hR).mp hx
  refine ⟨hfp, ?_⟩
  have hi := sharp_inverse_unit μ (fun x => f x/R) hg hg0 hm ha hC hgtube
  have hcpos : 0 < R^(-m) := Real.rpow_pos_of_pos hR _
  calc
    _ = ∫⁻ x, ENNReal.ofReal (R^(-m)) * ENNReal.ofReal ((f x/R)^(-m)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfp] with x hx
      rw [ENNReal.ofReal_rpow_of_pos hx, ← ENNReal.ofReal_mul hcpos.le,
        Real.div_rpow hx.le hR.le]
      congr 1
      exact (mul_div_cancel₀ _ hcpos.ne').symm
    _ = ENNReal.ofReal (R^(-m)) * (∫⁻ x, ENNReal.ofReal ((f x/R)^(-m)) ∂μ) :=
      lintegral_const_mul _ (hg.pow_const _).ennreal_ofReal
    _ ≤ ENNReal.ofReal (R^(-m)) *
        (ENNReal.ofReal B + ENNReal.ofReal (C*m/(a-m))) :=
      mul_le_mul' le_rfl (hi.trans (add_le_add hmass le_rfl))
    _ = _ := by
      rw [← ENNReal.ofReal_add hB (by positivity), ← ENNReal.ofReal_mul hcpos.le]
      congr 1
      ring

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma affine_tube_cover_radius (L : AffineSubspace ℝ E) [Nonempty L]
    (z : E) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3*R/t)^Module.finrank ℝ L.direction ∧
      ∀ x : E, dist x z ≤ R → Metric.infDist x L ≤ t →
        ∃ y ∈ s, dist x (R • (y:E) + (orthogonalProjection L z : E)) ≤ 2*t := by
  classical
  have hr : 0 < t/R := div_pos ht hR
  have hr1 : t/R ≤ 1 := (div_le_one hR).2 htR
  obtain ⟨s, _, hcard, hnet⟩ := NoiselessRegression.exists_unit_ball_net
    (E := L.direction) hr hr1
  refine ⟨s, ?_, ?_⟩
  · convert hcard using 1
    congr 1
    field_simp
  · intro x hx hdist
    let v : L.direction := L.direction.orthogonalProjectionOnto (x-z)
    have hv : ‖v‖ ≤ R := by
      apply (L.direction.norm_orthogonalProjectionOnto_apply_le (x-z)).trans
      simpa only [dist_eq_norm] using hx
    have hvnorm : ‖R⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      calc
        _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    obtain ⟨y, hy, hclose⟩ := hnet (R⁻¹ • v) hvnorm
    refine ⟨y, hy, ?_⟩
    have hscaled : dist (v:E) (R • (y:E)) ≤ t := by
      have heq : (v:E) = R • (R⁻¹ • (v:E)) := by simp [smul_smul, hR.ne']
      rw [heq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
      calc
        _ ≤ R * (t/R) := mul_le_mul_of_nonneg_left hclose hR.le
        _ = t := mul_div_cancel₀ _ hR.ne'
    have hproj : (orthogonalProjection L x : E) =
        (v:E) + (orthogonalProjection L z : E) := by
      have h := (orthogonalProjection L).map_vadd z (x-z)
      simpa only [vadd_eq_add, sub_add_cancel, orthogonalProjection_contLinear,
        AffineSubspace.coe_vadd] using congrArg (fun q : L => (q:E)) h
    have hpd : dist (orthogonalProjection L x : E)
        (R • (y:E) + (orthogonalProjection L z : E)) ≤ t := by
      rw [hproj, dist_add_right]
      exact hscaled
    have hxp : dist x (orthogonalProjection L x : E) ≤ t := by
      rwa [dist_orthogonalProjection_eq_infDist]
    calc
      _ ≤ dist x (orthogonalProjection L x : E) +
          dist (orthogonalProjection L x : E) (R • (y:E) + (orthogonalProjection L z : E)) :=
        dist_triangle _ _ _
      _ ≤ t+t := add_le_add hxp hpd
      _ = 2*t := by ring

end Geometry

section AmbientMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambient_tube_radius_factors (j : ℕ) (β : ℝ) {R t : ℝ} (ht : 0 < t) :
    (3*R/t)^j * (2*t)^β = (3:ℝ)^j * (2:ℝ)^β * R^j * t^(β-(j:ℝ)) := by
  rw [div_pow, mul_pow, Real.mul_rpow (by norm_num) ht.le,
    Real.rpow_sub_natCast ht.ne']
  ring

lemma ambient_tube {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    μ {x | Metric.infDist x L ≤ t} ≤ ENNReal.ofReal
      ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H *
        R^Module.finrank ℝ L.direction * t^(β-(Module.finrank ℝ L.direction:ℝ))) := by
  classical
  obtain ⟨s, hcard, hcover⟩ := affine_tube_cover_radius L z hR ht htR
  let c : L.direction → E := fun y => R • (y:E) + (orthogonalProjection L z : E)
  have hsub : {x | Metric.infDist x L ≤ t} ≤ᵐ[μ]
      ⋃ y ∈ s, Metric.closedBall (c y) (2*t) := by
    filter_upwards [μ.support_mem_ae] with x hx
    intro hxL
    have hxR : dist x z ≤ R := hsupport hx
    obtain ⟨y, hy, hxy⟩ := hcover x hxR hxL
    exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩
  calc
    _ ≤ μ (⋃ y ∈ s, Metric.closedBall (c y) (2*t)) := measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, μ (Metric.closedBall (c y) (2*t)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal (H*(2*t)^β) :=
      Finset.sum_le_sum fun y _ => hball (c y) _ (by positivity)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (H*(2*t)^β) := by simp
    _ ≤ ENNReal.ofReal ((3*R/t)^Module.finrank ℝ L.direction) *
        ENNReal.ofReal (H*(2*t)^β) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = H * ((3*R/t)^Module.finrank ℝ L.direction * (2*t)^β) := by ring
        _ = _ := by rw [ambient_tube_radius_factors _ _ ht]; ring

omit [BorelSpace E] in
lemma ambient_mass_bound {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β)) :
    μ univ ≤ ENNReal.ofReal (H * R^β) := by
  calc
    _ ≤ μ (Metric.closedBall z R) := by
      apply measure_mono_ae
      filter_upwards [μ.support_mem_ae] with x hx
      intro _
      exact hsupport hx
    _ ≤ _ := hball z R hR

lemma ambient_tube_scaled {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    μ {x | Metric.infDist x L ≤ R*t} ≤ ENNReal.ofReal
      (((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β) *
        t^(β-(Module.finrank ℝ L.direction:ℝ))) := by
  refine (ambient_tube hR hsupport hball L (mul_pos hR ht)
    (by nlinarith)).trans_eq ?_
  congr 1
  rw [Real.mul_rpow hR.le ht.le]
  have heq : R^Module.finrank ℝ L.direction * R^(β-(Module.finrank ℝ L.direction:ℝ)) = R^β := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ = ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H) *
      (R^Module.finrank ℝ L.direction * R^(β-(Module.finrank ℝ L.direction:ℝ))) *
      t^(β-(Module.finrank ℝ L.direction:ℝ)) := by ring
    _ = _ := by rw [heq]

lemma ambient_inverse_moment {μ : Measure E} {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {m : ℕ} (hm : 0 < m)
    (hgap : (Module.finrank ℝ L.direction:ℝ) + (m:ℝ) < β) :
    (∀ᵐ x ∂μ, 0 < Metric.infDist x L) ∧
    (∫⁻ x, (ENNReal.ofReal (Metric.infDist x L)) ^ (-(m:ℝ)) ∂μ) ≤
      ENNReal.ofReal (J β m (Module.finrank ℝ L.direction) * H * R^(β-(m:ℝ))) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi := sharp_inverse_scaled μ (fun x => Metric.infDist x L)
    (Metric.continuous_infDist_pt _).measurable (fun _ => Metric.infDist_nonneg)
    hm' (show (m:ℝ) < β-(Module.finrank ℝ L.direction:ℝ) by linarith)
    (show 0 ≤ H*R^β by positivity)
    (show 0 ≤ (3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β by positivity)
    hR (ambient_mass_bound hR hsupport hball)
    (fun t ht ht1 => ambient_tube_scaled hR hsupport hball L ht ht1)
  refine ⟨hi.1, hi.2.trans_eq ?_⟩
  congr 1
  have heq : H*R^β + ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β) *
      (m:ℝ)/(β-(Module.finrank ℝ L.direction:ℝ)-(m:ℝ)) =
      J β m (Module.finrank ℝ L.direction) * H * R^β := by
    unfold J
    ring
  rw [heq, mul_assoc, ← Real.rpow_add hR]
  congr 2

end AmbientMoments

lemma J_pos {β : ℝ} {m j : ℕ} (hgap : (j:ℝ)+(m:ℝ)<β) : 0 < J β m j := by
  unfold J
  have hd : 0 < β-(j:ℝ)-(m:ℝ) := by linarith
  positivity

lemma J_mono {β : ℝ} {m j k : ℕ} (hjk : j ≤ k)
    (hgap : (k:ℝ)+(m:ℝ)<β) : J β m j ≤ J β m k := by
  have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
  unfold J
  apply add_le_add le_rfl
  apply div_le_div₀
  · positivity
  · gcongr
    norm_num
  · linarith
  · linarith

section ReplicaExact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open NoiselessRegression InnerProductSpace

lemma ambient_inverse_moment_le {μ : Measure E} {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {m k : ℕ} (hm : 0 < m)
    (hdim : Module.finrank ℝ L.direction ≤ k) (hgap : (k:ℝ)+(m:ℝ)<β) :
    (∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂μ) ≤
      ENNReal.ofReal (J β m k * H * R^(β-(m:ℝ))) := by
  have hdim' : (Module.finrank ℝ L.direction:ℝ) ≤ k := by exact_mod_cast hdim
  obtain ⟨ha, hi⟩ := ambient_inverse_moment hH hR hsupport hball L hm (by linarith)
  calc
    _ = ∫⁻ x, (ENNReal.ofReal (Metric.infDist x L)) ^ (-(m:ℝ)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ha] with x hx
      rw [ENNReal.ofReal_rpow_of_pos hx, Real.rpow_neg hx.le, Real.rpow_natCast, inv_pow]
    _ ≤ ENNReal.ofReal (J β m (Module.finrank ℝ L.direction) * H * R^(β-(m:ℝ))) := hi
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact J_mono hdim hgap

lemma replica_integral_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (p : E) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => μ)) ≤
      ∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ))) := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hngap : (n:ℝ)+(m:ℝ)<β := by push_cast at hgap; linarith
    have hinner (v : Fin n → E) :
        (∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂μ) ≤
          replicaWeight m p v * ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      apply mul_le_mul' le_rfl
      apply ambient_inverse_moment_le hH hR hsupport hball _ hm _ hngap
      rw [AffineSubspace.direction_mk']
      simpa only [Fintype.card_fin, Set.finrank] using
        finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂μ
          ∂Measure.pi (fun _ => μ) := lintegral_pi_snoc μ _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) ∂Measure.pi (fun _ => μ) :=
        lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => μ)) *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) :=
        lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) :=
        mul_le_mul' (ih (by linarith)) le_rfl
      _ = _ := by rw [Fin.prod_univ_castSucc]; rfl

lemma ae_replica_nondegenerate_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (p : E) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => μ),
      ∀ i, gramSchmidt ℝ (fun j => v j-p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc μ (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hngap : (n:ℝ)+(m:ℝ)<β := by push_cast at hgap; linarith
    filter_upwards [ih (by linarith)] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i-p)))
    have hdim : (Module.finrank ℝ L.direction:ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i-p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have ha := (ambient_inverse_moment hH hR hsupport hball L hm (by linarith)).1
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx.ne'
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

lemma measurable_joint_replicaWeight (m n : ℕ) :
    Measurable (fun v : E × (Fin n → E) => replicaWeight m v.1 v.2) := by
  have hs : Measurable (fun v : E × (Fin n → E) => fun j => v.2 j-v.1) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

lemma ae_joint_replica_independent {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    ∀ᵐ v : E × (Fin n → E) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun j => v.2 j-v.1) := by
  have hmeas : MeasurableSet {v : E × (Fin n → E) |
      ∀ i, gramSchmidt ℝ (fun j => v.2 j-v.1) i ≠ 0} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have h := (measurable_gramSchmidt i).comp
      (show Measurable (fun v : E × (Fin n → E) => fun j => v.2 j-v.1) by fun_prop)
    exact (measurableSet_eq_fun h measurable_const).compl
  have ha : ∀ᵐ v : E × (Fin n → E) ∂μ.prod (Measure.pi (fun _ => μ)),
      ∀ i, gramSchmidt ℝ (fun j => v.2 j-v.1) i ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    exact Filter.Eventually.of_forall fun p =>
      ae_replica_nondegenerate_exact hH hR hsupport hball hm p n hgap
  filter_upwards [ha] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

lemma joint_replica_integral_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    (∫⁻ v : E × (Fin n → E), replicaWeight m v.1 v.2
      ∂μ.prod (Measure.pi (fun _ => μ))) ≤
      ENNReal.ofReal (H^(n+1) * R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) *
        ∏ j : Fin n, J β m j) := by
  have hJ (j : Fin n) : 0 < J β m j := by
    apply J_pos
    have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    linarith
  have hfac (j : Fin n) : 0 ≤ J β m j * H * R^(β-(m:ℝ)) := by
    exact le_of_lt (mul_pos (mul_pos (hJ j) hH) (Real.rpow_pos_of_pos hR _))
  calc
    _ = ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => μ) ∂μ :=
      lintegral_prod _ (measurable_joint_replicaWeight m n).aemeasurable
    _ ≤ ∫⁻ _p, ∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ))) ∂μ :=
      lintegral_mono fun p => replica_integral_exact hH hR hsupport hball hm p n hgap
    _ = (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) * μ univ :=
      lintegral_const _
    _ ≤ (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) *
        ENNReal.ofReal (H*R^β) := mul_le_mul' le_rfl (ambient_mass_bound hR hsupport hball)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hfac j),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hfac j)]
      congr 1
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.rpow_mul_natCast hR.le]
      have heq : R^((β-(m:ℝ))*(n:ℝ)) * R^β =
          R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) := by
        rw [← Real.rpow_add hR]
        congr 1
        push_cast
        ring
      calc
        _ = (H^n*H) * (R^((β-(m:ℝ))*(n:ℝ)) * R^β) * ∏ j : Fin n, J β m j := by ring
        _ = _ := by rw [← pow_succ, heq]

end ReplicaExact

lemma specialized_J_bound (d m p : ℕ) (hd : 16 ≤ d) (hp : p=d/8)
    (_ : 1 ≤ m) (hmp : m ≤ p) (β : ℝ)
    (hβlo : ((d:ℝ)-1)/2 ≤ β) (hβhi : β ≤ (d:ℝ)/2) :
    ∀ j : ℕ, j ≤ p-2 →
      ((d:ℝ)-1)/2 - 2*(p:ℝ) + 2 ≤ β-(j:ℝ)-(m:ℝ) ∧
      (d:ℝ)/4 + 3/2 ≤ ((d:ℝ)-1)/2 - 2*(p:ℝ) + 2 ∧
      J β m j ≤ (7:ℝ)^d := by
  have hp2 : 2 ≤ p := by omega
  have hp8 : p*8 ≤ d := by rw [hp]; exact Nat.div_mul_le_self d 8
  have hp8' : (p:ℝ)*8 ≤ d := by exact_mod_cast hp8
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hm' : (m:ℝ) ≤ p := by exact_mod_cast hmp
  intro j hj
  have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by omega)
  have hmargin : ((d:ℝ)-1)/2-2*(p:ℝ)+2 ≤ β-(j:ℝ)-(m:ℝ) := by linarith
  have hdim : (d:ℝ)/4+3/2 ≤ ((d:ℝ)-1)/2-2*(p:ℝ)+2 := by linarith
  refine ⟨hmargin, hdim, ?_⟩
  have hgap : 0 < β-(j:ℝ)-(m:ℝ) := by linarith
  have hquot : (m:ℝ)/(β-(j:ℝ)-(m:ℝ)) ≤ 1 := by
    rw [div_le_one hgap]
    linarith
  have h3 : (3:ℝ)^j ≤ (3:ℝ)^d := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h2 : (2:ℝ)^β ≤ (2:ℝ)^d := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  calc
    J β m j = 1 + (3:ℝ)^j * (2:ℝ)^β * ((m:ℝ)/(β-(j:ℝ)-(m:ℝ))) := by unfold J; ring
    _ ≤ 1 + (3:ℝ)^j * (2:ℝ)^β * 1 := by gcongr
    _ ≤ 1 + (3:ℝ)^d * (2:ℝ)^d := by rw [mul_one]; gcongr
    _ = 1 + (6:ℝ)^d := by rw [← mul_pow]; norm_num
    _ ≤ (7:ℝ)^d := by
      simpa only [one_pow, show (1:ℝ)+6=7 by norm_num] using pow_add_pow_le (show (0:ℝ) ≤ 1 by norm_num)
        (show (0:ℝ) ≤ 6 by norm_num) (show d ≠ 0 by omega)

lemma specialized_gram_product_bound (d m p : ℕ) (hd : 16 ≤ d) (hp : p=d/8)
    (hm : 1 ≤ m) (hmp : m ≤ p) (β : ℝ)
    (hβlo : ((d:ℝ)-1)/2 ≤ β) (hβhi : β ≤ (d:ℝ)/2)
    (H R : ℝ) (hH : 0 < H) (hR : 0 < R) :
    H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (∏ j : Fin (p-1), J β m j) ≤
      (7:ℝ)^(d*(p-1)) * H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) := by
  have hp2 : 2 ≤ p := by omega
  have hs := specialized_J_bound d m p hd hp hm hmp β hβlo hβhi
  have hprod : (∏ j : Fin (p-1), J β m j) ≤ (7:ℝ)^(d*(p-1)) := by
    calc
      _ ≤ ∏ _j : Fin (p-1), (7:ℝ)^d := by
        apply Finset.prod_le_prod₀
        · intro j _
          apply (J_pos ?_).le
          have hh := hs j (by have := j.isLt; omega)
          have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
          linarith [hh.1, hh.2.1]
        · intro j _
          exact (hs j (by have := j.isLt; omega)).2.2
      _ = _ := by simp [← pow_mul]
  calc
    _ ≤ H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (7:ℝ)^(d*(p-1)) := by gcongr
    _ = _ := by ring

def AmbientGramStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (∀ (d m p : ℕ),
    letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
    letI : PseudoMetricSpace (Space d) :=
      PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)
    letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
    letI : Module ℝ (Space d) := WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)
    1 ≤ d → 1 ≤ m → 2 ≤ p →
    ∀ β R H : ℝ, (m : ℝ) + (p : ℝ) - two < β → 0 < R → 0 < H →
    ∀ (μ : Measure (Space d)), IsFiniteMeasure μ →
    ∀ z : Space d, μ.support ⊆ Metric.closedBall z R →
    AmbientBallBound μ H β →
    (∀ (j : ℕ), j ≤ p-2 → ∀ L : AffineSubspace ℝ (Space d),
      Nonempty L → Module.finrank ℝ L.direction = j →
      (∀ t : ℝ, 0 < t → t ≤ R →
        μ {s | Metric.infDist s L ≤ t} ≤
          ENNReal.ofReal (three^j * two^β * H * R^j * t^(β-(j:ℝ)))) ∧
      (∫⁻ s, (ENNReal.ofReal (Metric.infDist s L)) ^ (-(m:ℝ)) ∂μ) ≤
        ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) ∧
    (∀ᵐ v : Space d × (Fin (p-1) → Space d)
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ)),
      LinearIndependent ℝ (fun i => v.2 i - v.1)) ∧
    (∫⁻ v : Space d × (Fin (p-1) → Space d), InverseGram m v
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ))) ≤
      ENNReal.ofReal (H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) *
        ∏ j : Fin (p-1), J β m j)) ∧
  (∃ C : ℝ, 1 ≤ C ∧ ∀ (d m p : ℕ), 16 ≤ d → p = d/8 →
    1 ≤ m → m ≤ p → ∀ β : ℝ, ((d:ℝ)-1)/two ≤ β → β ≤ (d:ℝ)/two →
    (∀ j : ℕ, j ≤ p-2 →
      ((d:ℝ)-1)/two - two*(p:ℝ) + two ≤ β-(j:ℝ)-(m:ℝ) ∧
      (d:ℝ)/four + three/two ≤ ((d:ℝ)-1)/two - two*(p:ℝ) + two ∧
      J β m j ≤ C^d) ∧
    (∀ H R : ℝ, 0 < H → 0 < R →
      H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (∏ j : Fin (p-1), J β m j) ≤
        C^(d*(p-1)) * H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ))))

theorem ambient_gram : AmbientGramStatement := by
  constructor
  · intro d m p _hd hm hp β R H hβ hR hH μ hfin z hsupport hball
    let : IsFiniteMeasure μ := hfin
    have hm0 : 0 < m := by omega
    have hp1 : 1 ≤ p := by omega
    have hgap : ((p-1:ℕ):ℝ)+(m:ℝ)-1<β := by
      rw [Nat.cast_sub hp1]
      push_cast
      linarith
    refine ⟨?_, ?_, ?_⟩
    · intro j hj L hnonempty hdim
      let : Nonempty L := hnonempty
      have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by omega)
      constructor
      · intro t ht htR
        simpa only [hdim] using ambient_tube hR hsupport hball L ht htR
      · have hi := (ambient_inverse_moment hH hR hsupport hball L hm0
          (by rw [hdim]; linarith)).2
        simpa only [hdim] using hi
    · exact ae_joint_replica_independent hH hR hsupport hball hm0 (p-1) hgap
    · have hi := joint_replica_integral_exact hH hR hsupport hball hm0 (p-1) hgap
      simpa only [NoiselessRegression.replicaWeight_eq_det, InverseGram,
        Nat.sub_add_cancel hp1] using hi
  · refine ⟨7, by norm_num, ?_⟩
    intro d m p hd hp hm hmp β hβlo hβhi
    exact ⟨specialized_J_bound d m p hd hp hm hmp β hβlo hβhi,
      specialized_gram_product_bound d m p hd hp hm hmp β hβlo hβhi⟩

end MemoryPrecision


end

end OAI
