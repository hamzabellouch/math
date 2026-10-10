import OAI.Geometry.Perimeter.Regularity.SupportAffineEstimate

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem constant_zero_of_quartic_bound {b M δ : ℝ} (hδ : 0<δ)
    (hb : ∀ r : ℝ, 0<r → r<δ → b^2≤M*r^4) : b=0 := by
  have ht : Tendsto (fun r : ℝ ↦ M*r^4) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0)).pow 4).const_mul M).mono_left nhdsWithin_le_nhds
  have hzero : b^2≤0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht (by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r hr hrδ
    exact hb r hr hrδ)
  nlinarith [sq_nonneg b]

theorem exists_full_support_improvement_constant (n : ℕ) (hn : 1<n)
    (D : ℝ) (hD : 0≤D) :
    ∃ K : ℝ, 0<K ∧ ∀ (E : ℕ → Set (Euc n)),
      (∀ i, IsLocallyPerimeterMinimizing (E i)) →
      (∀ i, (0:Euc n)∈perimeterSupport (E i)) →
      ∀ (v : Euc n) (φ w : normalPlane v → ℝ), Continuous φ → HasCompactSupport φ →
      (∀ y, 0≤φ y) →
      (∀ y∈Metric.ball (0:normalPlane v) (1/4), φ y=1) → Continuous w →
      ∀ (a : ℕ → ℝ), (∀ i, 0<a i) →
      (∀ i x, x∈perimeterSupport (E i) ∩ Metric.ball 0 4 → |inner ℝ v x|≤a i) →
      ∀ (ℓ : Euc n →L[ℝ] ℝ) (b : ℝ),
      (∀ x∈Metric.ball (0:Euc n) (1/4), |w (normalProjection v x)-b-ℓ x|≤D*‖x‖^2) →
      Tendsto (fun i ↦ ∫ x in Metric.ball 0 4,
        normalWindowQuadratic v φ w (a i) (2*a i) x ∂perimeterMeasure (E i)) atTop (𝓝 0) →
      b=0 ∧ ∀ r : ℝ, 0<r → r<1/8 → ∀ᶠ i in atTop,
        ∀ p∈perimeterSupport (E i) ∩ Metric.ball 0 r,
          |inner ℝ v p/a i-ℓ p|≤K*r^2 := by
  obtain ⟨C,hC,hmean⟩ := exists_minimizing_linear_mean_value_constant n hn
  obtain ⟨G,hG,hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  let A := C*(2+64*D^2*G)
  have hA : 0≤A := by dsimp [A]; positivity
  let K := A+1
  have hK : 0<K := by dsimp [K]; linarith
  have hAK : A≤K^2 := by dsimp [K]; nlinarith [sq_nonneg A]
  refine ⟨K,hK,fun E hmin hzero v φ w hφ hcφ hpφ hφone hw a ha hh ℓ b htaylor htrace ↦ ?_⟩
  let Q : ℕ → ℝ := fun i ↦ ∫ x in Metric.ball 0 4,
    normalWindowQuadratic v φ w (a i) (2*a i) x ∂perimeterMeasure (E i)
  have hest (r : ℝ) (hr : 0<r) (hrb : r<1/8) (i : ℕ)
      (p : Euc n) (hp : p∈perimeterSupport (E i) ∩ Metric.ball 0 r) :
      (inner ℝ v p/a i-ℓ p-b)^2≤C/r^(n-1)*(2*Q i+(8*D*r^2)^2*(G*r^(n-1))) :=
    minimizing_support_taylor_estimate (hmin i) hC hG.le (hmean (E i) (hmin i))
      (hgrowth (E i) (hmin i)) v hφ hcφ hpφ hφone hw (ha i) hD hr hrb ℓ htaylor
      (hh i) hp.1 hp.2
  have hb : b=0 := by
    apply constant_zero_of_quartic_bound (δ := 1/8) (M := 64*C*D^2*G) (by norm_num)
    intro r hr hrb
    have he (i : ℕ) : b^2≤C/r^(n-1)*(2*Q i+(8*D*r^2)^2*(G*r^(n-1))) := by
      simpa only [inner_zero_right,zero_div,map_zero,sub_zero,zero_sub,neg_sq] using
        hest r hr hrb i 0 ⟨hzero i,Metric.mem_ball_self hr⟩
    have ht : Tendsto (fun i ↦ C/r^(n-1)*(2*Q i+(8*D*r^2)^2*(G*r^(n-1))))
        atTop (𝓝 (C/r^(n-1)*((8*D*r^2)^2*(G*r^(n-1))))) := by
      simpa only [mul_zero,zero_add] using (htrace.const_mul 2 |>.add_const ((8*D*r^2)^2*(G*r^(n-1)))).const_mul (C/r^(n-1))
    have h := le_of_tendsto_of_tendsto' tendsto_const_nhds ht he
    have heq : C/r^(n-1)*((8*D*r^2)^2*(G*r^(n-1)))=(64*C*D^2*G)*r^4 := by
      field_simp [ne_of_gt hr]
      ring
    rw [heq] at h
    exact h
  refine ⟨hb,fun r hr hrb ↦ ?_⟩
  have hsmall : ∀ᶠ i in atTop, Q i<r^(n-1)*r^4 :=
    htrace.eventually (gt_mem_nhds (by positivity : (0:ℝ)<r^(n-1)*r^4))
  filter_upwards [hsmall] with i hi
  intro p hp
  have h := hest r hr hrb i p hp
  rw [hb,sub_zero] at h
  have hsq : (inner ℝ v p/a i-ℓ p)^2≤A*r^4 := by
    apply h.trans
    calc
      _ ≤ C/r^(n-1)*(2*(r^(n-1)*r^4)+(8*D*r^2)^2*(G*r^(n-1))) := by gcongr
      _ = A*r^4 := by dsimp [A]; field_simp; ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤K*r^2)).mp
  rw [sq_abs]
  apply hsq.trans
  calc
    A*r^4 ≤ K^2*r^4 := mul_le_mul_of_nonneg_right hAK (by positivity)
    _ = (K*r^2)^2 := by ring

end RPISingularHarnack

end

end OAI
