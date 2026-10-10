import OAI.Probability.SLE.Angle.ActualAngleWarmup
import OAI.Probability.SLE.Geometry.ExtendedDiskAngle
import OAI.Probability.SLE.Geometry.NormalizedDiskDensity

namespace OAI

/-! Normalization preserves the full stopped argument, which is the state
variable needed by the finite-centered transition kernel. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.normalized_restart_stopped_arg
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (w : ℂ) (u v : ℝ)
    (hbase : fullRadius G T (F T ((a : ℂ) * w + (U T : ℂ))) =
      (2 * (F T ((a : ℂ) * w + (U T : ℂ))).im) * Real.exp (-u))
    (hfinite : radiusLevelTime β G' w v < ∞) :
    radiusLevelTime γ G (F T ((a : ℂ) * w + (U T : ℂ))) (u + v) < ∞ ∧
    Complex.arg (G (radiusLevelTime γ G
        (F T ((a : ℂ) * w + (U T : ℂ))) (u + v)).toNNReal
        (F T ((a : ℂ) * w + (U T : ℂ))) -
      (U (radiusLevelTime γ G (F T ((a : ℂ) * w + (U T : ℂ)))
        (u + v)).toNNReal : ℂ)) =
    Complex.arg (G' (radiusLevelTime β G' w v).toNNReal w -
      (normalizedRestartDriver U T a (radiusLevelTime β G' w v).toNNReal : ℂ)) := by
  have hV : Continuous (normalizedRestartDriver U T a) := by
    unfold normalizedRestartDriver
    fun_prop
  obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hfinite
  have hs := radiusLevelTime_eq_of_live_level hV hb w v t ht hR
  have hp := (hw.normalized_restart_level_of_live_source hU T a ha hb w u v hbase t ht hR).2
  refine ⟨by rw [hp]; exact ENNReal.coe_lt_top, ?_⟩
  rw [hp, hs, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
  have hbup := normalized_restart_witness T a ha hb
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have htu : (a : ℂ) * w ∈ survivingDomain (sourceScaleTrace a β) (a ^ 2 * t) := by
    rw [source_scale_domain_iff a _ ha β, source_scale_time_mul_sq a t ha,
      mul_div_cancel_left₀ w haC]
    exact ht
  have hc := hw.restart_centered_value T hbup (a ^ 2 * t) ((a : ℂ) * w) htu
  rw [sourceScaleChart, source_scale_time_mul_sq a t ha,
    mul_div_cancel_left₀ w haC] at hc
  have hscale : (a : ℂ) * G' t w - ((U (T + a ^ 2 * t) - U T : ℝ) : ℂ) =
      (a : ℂ) * (G' t w - (normalizedRestartDriver U T a t : ℂ)) := by
    rw [normalizedRestartDriver, Complex.ofReal_div]
    field_simp
  rw [hc, hscale]
  exact Complex.arg_real_mul _ (show (0:ℝ)<(a:ℝ) from ha)

def canonicalStoppedAngle (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0,ℝ))) : ℝ :=
  if canonicalRadiusLevel κ q < ∞ then (canonicalStoppedCenter κ q).arg else 0

lemma canonicalStoppedAngle_measurable (κ : ℝ) : Measurable (canonicalStoppedAngle κ) :=
  Measurable.ite (measurableSet_lt (canonicalRadiusLevel_measurable κ) measurable_const)
    (canonicalStoppedCenter_measurable κ).carg measurable_const

lemma canonicalStoppedAngle_eq (κ : ℝ) (p : C(ℝ≥0,ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) (hfinite : radiusLevelTime γ G z u < ∞) :
    canonicalStoppedAngle κ (u,z,p)=
      (G (radiusLevelTime γ G z u).toNNReal z-
        ((Real.sqrt κ*p (radiusLevelTime γ G z u).toNNReal:ℝ):ℂ)).arg := by
  rw [canonicalStoppedAngle,canonicalRadiusLevel_eq κ p hw u hu z,ite_eq_left hfinite,
    canonicalStoppedCenter_eq κ p hw u hu z hfinite]


lemma extendedMarkedAngle_at_finite_radius {Ω : Type*}
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (u : ℝ) (ω : Ω) (hf : radiusLevelTime (γ ω) (G ω) z u<∞) :
    extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω =
      (G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
        ((Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ):ℂ)).arg := by
  obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top (γ ω) (G ω) z u hf
  have he := radiusLevelTime_eq_of_live_level ((hc ω).const_mul _) (hw ω) z u t ht hR
  have htime : WithTop.untopD 0 (radiusLevelTime (γ ω) (G ω) z u)=t := by
    change (radiusLevelTime (γ ω) (G ω) z u).toNNReal=t
    rw [he,ENNReal.toNNReal_coe]
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  change extendedMarkedAngle κ B γ G σ z ω = _
  dsimp only [extendedMarkedAngle]
  rw [ite_eq_right (show σ ω≠⊤ from ne_of_lt hf),
    stoppedMarkedCenter_time_congr κ B γ G _ (fun _ => t) z ω htime,
    stoppedMarkedCenter_eq κ B γ G (fun _ => t) z ω ht,he,ENNReal.toNNReal_coe]

lemma IsCapacityTwoWitness.normalized_disk_stopped_arg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (T a : ℝ≥0) (ha : 0 < a) (p : C(ℝ≥0,ℝ))
    {β : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hb : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) β G' F')
    (hdriver : (fun t => Real.sqrt κ*p t)=normalizedRestartDriver U T a)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (z : ℂ)
    (hz : z ∈ survivingDomain γ T)
    (hpolar : G T z=(U T:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T z=(2*z.im)*Real.exp (-u))
    (hfinite : radiusLevelTime γ G z (u+v)<∞) :
    (G (radiusLevelTime γ G z (u+v)).toNNReal z-
      (U (radiusLevelTime γ G z (u+v)).toNNReal:ℂ)).arg =
        canonicalStoppedAngle κ (v,Target.diskMapInv θ 0,p) := by
  have hb' : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F' := by
    rwa [hdriver] at hb
  have hF : F T ((a:ℂ)*Target.diskMapInv θ 0+(U T:ℂ))=z := by
    rw [Target.diskMapInv_zero,add_comm,← hpolar]
    exact hw.2.2.2.2.2.2.2.1 T z hz
  have hbase' : fullRadius G T (F T ((a:ℂ)*Target.diskMapInv θ 0+(U T:ℂ)))=
      (2*(F T ((a:ℂ)*Target.diskMapInv θ 0+(U T:ℂ))).im)*Real.exp (-u) := by
    simpa only [hF] using hbase
  have hf := (hw.normalized_restart_radius_finite_iff hU T a ha hb'
    (Target.diskMapInv θ 0) (Target.diskMapInv_maps hθ (by simp)) u v hu hv hbase').mp
      (by simpa only [hF] using hfinite)
  have he := (hw.normalized_restart_stopped_arg hU T a ha hb'
    (Target.diskMapInv θ 0) u v hbase' hf).2
  rw [hF] at he
  rw [canonicalStoppedAngle_eq κ p hb v hv.le _ hf,
    congrFun hdriver (radiusLevelTime β G' (Target.diskMapInv θ 0) v).toNNReal]
  exact he

end SLEExactGauge

end

end OAI
