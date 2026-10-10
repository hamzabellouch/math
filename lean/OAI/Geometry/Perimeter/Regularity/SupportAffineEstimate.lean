import OAI.Geometry.Perimeter.Regularity.QuadraticMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem normalWindowQuadratic_integrableOn {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (v : Euc n) {φ w : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hw : Continuous w)
    {a b R : ℝ} (hb : 0≤b) (hR : 0<R) :
    IntegrableOn (normalWindowQuadratic v φ w a b) (Metric.ball 0 R) (perimeterMeasure E) := by
  have hi2 := normalWindowTest_integrableOn hmin v hφ hcφ hb hR 2
  have hi1 := normalWindowTest_integrableOn hmin v (hφ.mul hw) hcφ.mul_right hb hR 1
  have hi0 := normalWindowTest_integrableOn hmin v (hφ.mul (hw.pow 2)) hcφ.mul_right hb hR 0
  rw [normalWindowQuadratic_expand]
  exact ((hi2.const_mul ((a⁻¹)^2)).sub (hi1.const_mul (2/a))).add hi0

theorem normalWindowQuadratic_nonneg (v : Euc n) {φ w : normalPlane v → ℝ}
    (hφ : ∀ y, 0≤φ y) (a b : ℝ) (x : Euc n) :
    0≤normalWindowQuadratic v φ w a b x := by
  dsimp only [normalWindowQuadratic]
  exact Set.indicator_nonneg (fun x _ ↦ mul_nonneg (hφ _) (sq_nonneg _)) x

theorem exists_minimizing_linear_mean_value_constant (n : ℕ) (hn : 1<n) :
    ∃ C : ℝ, 0<C ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ p ∈ perimeterSupport E, ∀ r : ℝ, 0<r → ∀ (L : Euc n →L[ℝ] ℝ) (b : ℝ),
        (L p-b)^2≤C/r^(n-1)*∫ x in Metric.ball p r, (L x-b)^2 ∂perimeterMeasure E := by
  obtain ⟨C,hC,h⟩ := exists_minimizing_height_mean_value_constant n hn
  refine ⟨C,hC,fun E hE p hp r hr L b ↦ ?_⟩
  simpa only [InnerProductSpace.toDual_symm_apply] using
    h E hE p hp r hr ((InnerProductSpace.toDual ℝ (Euc n)).symm L) b

theorem minimizing_affine_error_from_trace {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {C G : ℝ} (hC : 0<C)
    (hmean : ∀ p ∈ perimeterSupport E, ∀ r : ℝ, 0<r → ∀ (L : Euc n →L[ℝ] ℝ) (b : ℝ),
      (L p-b)^2≤C/r^(n-1)*∫ x in Metric.ball p r, (L x-b)^2 ∂perimeterMeasure E)
    (hgrowth : ∀ p r, 0<r → perimeter E (Metric.ball p r)≤ENNReal.ofReal (G*r^(n-1)))
    (hG : 0≤G) {Q : Euc n → ℝ}
    (hQ : IntegrableOn Q (Metric.ball 0 4) (perimeterMeasure E))
    (hQ0 : ∀ x, 0≤Q x) {L : Euc n →L[ℝ] ℝ} {b T r : ℝ}
    (hr : 0<r) (hrb : r<1) {p : Euc n} (hp : p∈perimeterSupport E)
    (hpb : p∈Metric.ball 0 r)
    (hbound : ∀ x∈perimeterSupport E ∩ Metric.ball p r, (L x-b)^2≤2*Q x+T^2) :
    (L p-b)^2≤C/r^(n-1)*(2*(∫ x in Metric.ball 0 4, Q x ∂perimeterMeasure E)+T^2*(G*r^(n-1))) := by
  have hsub : Metric.ball p r ⊆ Metric.ball (0:Euc n) 4 := by
    intro x hx
    have hd := dist_triangle x p 0
    rw [Metric.mem_ball] at hx hpb ⊢
    linarith
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure ((perimeterMeasure E).restrict (Metric.ball p r)) := ⟨by
    rw [Measure.restrict_apply_univ,perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 p r hr⟩
  have hiA : IntegrableOn (fun x ↦ (L x-b)^2) (Metric.ball p r) (perimeterMeasure E) :=
    (((L.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall p r)).mono_set Metric.ball_subset_closedBall
  have hiQ := hQ.mono_set hsub
  have hs : ∀ᵐ x ∂perimeterMeasure E, x∈perimeterSupport E := by
    rw [← perimeterMeasure_support]; exact (perimeterMeasure E).support_mem_ae
  have hib : (∫ x in Metric.ball p r, (L x-b)^2 ∂perimeterMeasure E) ≤
      ∫ x in Metric.ball p r, 2*Q x+T^2 ∂perimeterMeasure E := by
    apply integral_mono_ae hiA ((hiQ.const_mul 2).add (integrable_const _))
    filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem measurableSet_ball] with x hx hxB
    exact hbound x ⟨hx,hxB⟩
  have hiQle := setIntegral_mono_set hQ (ae_of_all _ hQ0) (ae_of_all _ hsub)
  have hper : (perimeterMeasure E).real (Metric.ball p r)≤G*r^(n-1) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgrowth p r hr)
    rw [ENNReal.toReal_ofReal (mul_nonneg hG (pow_nonneg hr.le _))] at h
    simpa only [Measure.real,perimeterMeasure_open E Metric.isOpen_ball] using h
  apply (hmean p hp r hr L b).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ x in Metric.ball p r, 2*Q x+T^2 ∂perimeterMeasure E := hib
    _ = 2*(∫ x in Metric.ball p r, Q x ∂perimeterMeasure E)+T^2*(perimeterMeasure E).real (Metric.ball p r) := by
      rw [integral_add (hiQ.const_mul 2) (integrable_const _),integral_const_mul,integral_const]
      simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ,mul_comm]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hiQle (by norm_num))
      (mul_le_mul_of_nonneg_left hper (sq_nonneg _))

theorem minimizing_support_taylor_estimate {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {C G : ℝ} (hC : 0<C) (hG : 0≤G)
    (hmean : ∀ p ∈ perimeterSupport E, ∀ r : ℝ, 0<r → ∀ (L : Euc n →L[ℝ] ℝ) (b : ℝ),
      (L p-b)^2≤C/r^(n-1)*∫ x in Metric.ball p r, (L x-b)^2 ∂perimeterMeasure E)
    (hgrowth : ∀ p r, 0<r → perimeter E (Metric.ball p r)≤ENNReal.ofReal (G*r^(n-1)))
    (v : Euc n) {φ w : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hφ0 : ∀ y, 0≤φ y)
    (hφone : ∀ y∈Metric.ball (0:normalPlane v) (1/4), φ y=1)
    (hw : Continuous w) {a D r b : ℝ} (ha : 0<a) (hD : 0≤D)
    (hr : 0<r) (hrb : r<1/8) (ℓ : Euc n →L[ℝ] ℝ)
    (htaylor : ∀ x∈Metric.ball (0:Euc n) (1/4), |w (normalProjection v x)-b-ℓ x|≤D*‖x‖^2)
    (hh : ∀ x∈perimeterSupport E ∩ Metric.ball 0 4, |inner ℝ v x|≤a)
    {p : Euc n} (hp : p∈perimeterSupport E) (hpb : p∈Metric.ball 0 r) :
    (inner ℝ v p/a-ℓ p-b)^2 ≤ C/r^(n-1)*
      (2*(∫ x in Metric.ball 0 4, normalWindowQuadratic v φ w a (2*a) x ∂perimeterMeasure E)+
        (8*D*r^2)^2*(G*r^(n-1))) := by
  let L : Euc n →L[ℝ] ℝ := a⁻¹ • innerSL ℝ v - ℓ
  have hL (x : Euc n) : L x=inner ℝ v x/a-ℓ x := by
    simp only [L,sub_apply,smul_apply,smul_eq_mul]
    change a⁻¹*inner ℝ v x-ℓ x=inner ℝ v x/a-ℓ x
    ring
  rw [← hL]
  apply minimizing_affine_error_from_trace hmin hC hmean hgrowth hG
    (normalWindowQuadratic_integrableOn hmin v hφ hcφ hw (by positivity) (by norm_num))
    (normalWindowQuadratic_nonneg v hφ0 a (2*a)) hr (by linarith) hp hpb
  intro x hx
  have hxb : ‖x‖<2*r := by
    have hd := dist_triangle x p 0
    have hxB := hx.2
    rw [Metric.mem_ball] at hxB hpb
    simpa only [dist_zero_right] using (lt_of_le_of_lt hd (by linarith : dist x p+dist p 0<2*r))
  have hx4 : x∈Metric.ball (0:Euc n) 4 := by rw [Metric.mem_ball,dist_zero_right]; linarith
  have hxq : x∈Metric.ball (0:Euc n) (1/4) := by rw [Metric.mem_ball,dist_zero_right]; linarith
  have hproj : normalProjection v x∈Metric.ball (0:normalPlane v) (1/4) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact ((normalPlane v).norm_orthogonalProjectionOnto_apply_le x).trans_lt
      (by rw [Metric.mem_ball,dist_zero_right] at hxq; exact hxq)
  have heq : normalWindowQuadratic v φ w a (2*a) x=(inner ℝ v x/a-w (normalProjection v x))^2 := by
    rw [normalWindowQuadratic,Set.indicator_of_mem (show x∈{z:Euc n | |inner ℝ v z|≤2*a} from
      (hh x ⟨hx.1,hx4⟩).trans (by linarith)),hφone _ hproj,one_mul]
  have ht := htaylor x hxq
  have htx : |w (normalProjection v x)-b-ℓ x|≤4*D*r^2 := by
    apply ht.trans
    have hn0 := norm_nonneg x
    nlinarith [sq_nonneg (2*r-‖x‖),mul_nonneg hD (show 0≤4*r^2-‖x‖^2 by nlinarith)]
  rw [hL,heq]
  have hs := sq_le_sq₀ (abs_nonneg (w (normalProjection v x)-b-ℓ x)) (by positivity : 0≤4*D*r^2)
  have ht2 : (w (normalProjection v x)-b-ℓ x)^2≤(4*D*r^2)^2 := by
    simpa only [sq_abs] using hs.mpr htx
  nlinarith [sq_nonneg ((inner ℝ v x/a-w (normalProjection v x))-(w (normalProjection v x)-b-ℓ x)),
    sq_nonneg (D*r^2)]

end RPISingularHarnack

end

end OAI
