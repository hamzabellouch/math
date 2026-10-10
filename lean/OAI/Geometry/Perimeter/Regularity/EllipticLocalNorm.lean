import OAI.Geometry.Perimeter.Regularity.EllipticHodge

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def scalarNormLp (u : VectorL2 n) : Lp ℝ 2 (volume : Measure (Euc n)) :=
  (Lp.memLp u).norm.toLp (fun x ↦ ‖u x‖)

theorem scalarNormLp_ae (u : VectorL2 n) :
    (scalarNormLp u : Euc n → ℝ)=ᵐ[volume] fun x ↦ ‖u x‖ := MemLp.coeFn_toLp _

theorem scalarNormLp_norm (u : VectorL2 n) : ‖scalarNormLp u‖=‖u‖ := by
  rw [scalarNormLp,Lp.norm_toLp,eLpNorm_norm,Lp.norm_def]
  exact (Lp.memLp u).aestronglyMeasurable

def ballL2Mass (n : ℕ) (r : ℝ) : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure (Euc n))) 2 (measurableSet_ball : MeasurableSet (Metric.ball (0:Euc n) r))
    measure_ball_lt_top.ne (1:ℝ)‖

theorem localL1_le_L2 (u : VectorL2 n) (r : ℝ) :
    (∫ x in Metric.ball (0:Euc n) r, ‖u x‖) ≤ ballL2Mass n r * ‖u‖ := by
  rw [←scalarNormLp_norm u]
  have he : (∫ x in Metric.ball (0:Euc n) r, ‖u x‖)=
      ∫ x in Metric.ball (0:Euc n) r, scalarNormLp u x :=
    integral_congr_ae (ae_restrict_of_ae (scalarNormLp_ae u).symm)
  rw [he,←MeasureTheory.L2.inner_indicatorConstLp_one measurableSet_ball measure_ball_lt_top.ne]
  exact real_inner_le_norm _ _

theorem WeakHarmonicOn.congr_on {u w : Euc n → ℝ} {U : Set (Euc n)}
    (hu : WeakHarmonicOn u U) (hw : EqOn u w U) : WeakHarmonicOn w U := by
  intro φ hφ hcφ hsφ
  have he : (fun x ↦ w x*divergence (gradient φ) x)=
      (fun x ↦ u x*divergence (gradient φ) x) := by
    funext x
    by_cases hx : x∈U
    · rw [hw hx]
    · have hn : x∉tsupport φ := fun hh ↦ hx (hsφ hh)
      have hz : fderiv ℝ (gradient φ) x=0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh ↦ hn (tsupport_gradient_subset φ hh))
      simp [divergence,hz]
  rw [he]
  exact hu φ hφ hcφ hsφ

def localScalarComponent (u : VectorL2 n) (a : Euc n) : Euc n → ℝ :=
  (Metric.ball 0 1).indicator (fun x ↦ inner ℝ a (u x))

theorem localScalarComponent_integrable (u : VectorL2 n) (a : Euc n) :
    Integrable (localScalarComponent u a) volume := by
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  exact ((((innerSL ℝ a).comp_memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0:Euc n) 1)).mono_set Metric.ball_subset_closedBall

theorem localScalarComponent_L1 (u : VectorL2 n) (a : Euc n) :
    (∫ x, ‖localScalarComponent u a x‖) ≤ ‖a‖*ballL2Mass n 1*‖u‖ := by
  have he : (fun x ↦ ‖localScalarComponent u a x‖)=
      (Metric.ball 0 1).indicator (fun x ↦ ‖inner ℝ a (u x)‖) := by
    funext x
    simp only [localScalarComponent]
    by_cases hx : x∈Metric.ball (0:Euc n) 1 <;> simp [hx]
  rw [he,integral_indicator measurableSet_ball]
  have hI : IntegrableOn (fun x ↦ u x) (Metric.ball (0:Euc n) 1) volume :=
    integrableOn_Lp_of_measure_ne_top u (by norm_num) measure_ball_lt_top.ne
  calc
    _ ≤ ∫ x in Metric.ball (0:Euc n) 1, ‖a‖*‖u x‖ := integral_mono_ae
      (((((innerSL ℝ a).comp_memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0:Euc n) 1)).mono_set Metric.ball_subset_closedBall).norm
      (hI.norm.const_mul _) (ae_of_all _ fun x ↦ norm_inner_le_norm a (u x))
    _ = ‖a‖*(∫ x in Metric.ball (0:Euc n) 1, ‖u x‖) := integral_const_mul _ _
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (localL1_le_L2 u 1) (norm_nonneg a)

theorem localScalarComponent_weakHarmonic {u : VectorL2 n}
    (hd : DivFreeLpOn u (Metric.ball 0 1)) (hc : CurlFreeLpOn u (Metric.ball 0 1))
    (a : Euc n) : WeakHarmonicOn (localScalarComponent u a) (Metric.ball 0 1) := by
  apply (div_curl_weak_harmonic hd hc a).congr_on
  intro x hx
  change inner ℝ a (u x)=(Metric.ball (0:Euc n) 1).indicator (fun z ↦ inner ℝ a (u z)) x
  rw [Set.indicator_of_mem hx]

end RPISingularHarnack

end

end OAI
