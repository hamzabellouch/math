import OAI.Probability.SLE.Geometry.NormalizedDiskAngle

namespace OAI

/-! The actual finite-centered transition of the full angle, represented
by a measurable raw-driver kernel. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance angleKernelMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance angleKernelBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def canonicalAngleAverage (ν : Measure C(ℝ≥0,ℝ)) (κ v : ℝ)
    (f : ℝ → ℝ≥0∞) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, f (canonicalStoppedAngle κ (v,Target.diskMapInv θ 0,p))
    ∂ν.withDensity (fun p => canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p))

lemma canonicalAngleAverage_measurable (ν : Measure C(ℝ≥0,ℝ)) [SFinite ν]
    (κ v : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (canonicalAngleAverage ν κ v f) := by
  have hz : Measurable (fun θ => Target.diskMapInv θ 0) := by
    unfold Target.diskMapInv
    fun_prop
  let q : ℝ × C(ℝ≥0,ℝ) → ℝ × (ℂ × C(ℝ≥0,ℝ)) :=
    fun x => (v,Target.diskMapInv x.1 0,x.2)
  have hq : Measurable q := measurable_const.prodMk
    ((hz.comp measurable_fst).prodMk measurable_snd)
  have h := (((canonicalFiniteDensity_measurable κ).comp hq).mul
    (hf.comp ((canonicalStoppedAngle_measurable κ).comp hq))).lintegral_prod_right' (ν := ν)
  have he (θ : ℝ) : (∫⁻ p, canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p)*
      f (canonicalStoppedAngle κ (v,Target.diskMapInv θ 0,p)) ∂ν)=
      canonicalAngleAverage ν κ v f θ := by
    symm
    exact lintegral_withDensity_eq_lintegral_mul _
      ((canonicalFiniteDensity_measurable κ).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (hf.comp ((canonicalStoppedAngle_measurable κ).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  simpa only [q,Pi.mul_apply,Function.comp_apply,he] using h

lemma IsCapacityTwoWitness.normalized_disk_angle_test
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (T a : ℝ≥0) (ha : 0 < a) (p : C(ℝ≥0,ℝ))
    {β : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hb : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) β G' F')
    (hdriver : (fun t => Real.sqrt κ*p t)=normalizedRestartDriver U T a)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (hzH : z∈upperHalfPlane)
    (hpolar : G T z=(U T:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T z=(2*z.im)*Real.exp (-u)) (f : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (greenDensity κ U γ G T z/initialGreen κ z)*
        canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p)*
        f (canonicalStoppedAngle κ (v,Target.diskMapInv θ 0,p)) =
      ENNReal.ofReal (stoppedGreen κ U γ G z (u+v)/initialGreen κ z)*
        f ((G (radiusLevelTime γ G z (u+v)).toNNReal z-
          (U (radiusLevelTime γ G z (u+v)).toNNReal:ℂ)).arg) := by
  rw [← hw.normalized_disk_density hU κ T a ha p hb hdriver θ hθ z hz hzH hpolar u v hu hv hbase]
  by_cases ht : radiusLevelTime γ G z (u+v)<∞
  · rw [hw.normalized_disk_stopped_arg hU κ T a ha p hb hdriver θ hθ z hz hpolar u v hu hv hbase ht]
  · simp only [stoppedGreen,ite_eq_right ht,zero_div,ENNReal.ofReal_zero,zero_mul]

end SLEExactGauge

end

end OAI
