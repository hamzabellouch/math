import OAI.Probability.SLE.Mass.DiskLevelMoments

namespace OAI

/-! Uniform centered moments of the physical disk level masses. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

theorem diskLevelMass_centered_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : MeasurableSet K) (hKd : K ⊆ ball 0 1)
    (b : ℝ) (hb : 0<b) (hb1 : b≤1) (hbK : ∀ x∈K, b≤1-‖x‖^2)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (m : ℕ)
    (e : ℝ) (he : 0<e) (he1 : e≤1) (u : ℝ) (hu : 0≤u) :
    (∫⁻ ω in diskCenterHit γ G θ e, diskLevelMass κ θ B γ G u K ω ^ m ∂P) ≤
      ENNReal.ofReal (e^codimension κ)*centeredLevelMomentBound κ b 0 K m := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hE := measurableSet_diskCenterHit hm hc κ θ hθ γ G F hw e he he1
  have hW := (measurable_diskStoppedGreen hm hc κ θ u hu γ G F hw).ennreal_ofReal
  change (∫⁻ ω in diskCenterHit γ G θ e,
    (∫⁻ x in K, ENNReal.ofReal (diskStoppedGreen κ θ B γ G u ω x))^m ∂P) ≤ _
  rw [lintegral_mass_pow_eq (P.restrict (diskCenterHit γ G θ e)) (volume.restrict K)
    (fun ω x => ENNReal.ofReal (diskStoppedGreen κ θ B γ G u ω x)) hW m]
  have hk : Measurable (fun x : Fin m → ℂ =>
      cappedDistanceKernel (codimension κ) b (Fin.cons 0 x)) := by
    apply (measurable_cappedDistanceKernel _ _).comp
    apply Measurable.of_eval
    intro i
    exact Fin.cases measurable_const (fun j => measurable_pi_apply j) i
  have hbnd : (∫⁻ x : Fin m → ℂ, ∫⁻ ω in diskCenterHit γ G θ e,
      ∏ i, ENNReal.ofReal (diskStoppedGreen κ θ B γ G u ω (x i)) ∂P
      ∂Measure.pi (fun _ : Fin m => volume.restrict K)) ≤
      ENNReal.ofReal (multipointConstant κ (m+1)*e^codimension κ)*
        ∫⁻ x : Fin m → ℂ, cappedDistanceKernel (codimension κ) b (Fin.cons 0 x)
          ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
    rw [← lintegral_const_mul _ hk]
    apply lintegral_mono_ae
    filter_upwards [ae_tuple_mem (ι:=Fin m) K hK,ae_fin_cons_injective m K 0] with x hx hi
    have h := diskStoppedGreen_centered_product_bound hB hm hBm hc h0 hκ hκ8
      γ G F hw hgrowth θ hθ m x (fun i => hKd (hx i)) hi b hb hb1
      (fun i => hbK _ (hx i)) e he u
    rw [lintegral_indicator hE] at h
    simpa only [ENNReal.ofReal_prod_of_nonneg
      (fun i _ => diskStoppedGreen_nonneg hw u _ (x i))] using h
  apply hbnd.trans_eq
  rw [ENNReal.ofReal_mul (multipointConstant_pos _ _).le]
  unfold centeredLevelMomentBound
  ring

theorem uniform_diskLevelMass_centered_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKd : K ⊆ ball 0 1)
    (b : ℝ) (hb : 0<b) (hb1 : b≤1) (hbK : ∀ x∈K, b≤1-‖x‖^2) (m : ℕ) :
    ∃ M : ℝ≥0∞, M<∞ ∧ ∀ θ∈Ioo (0:ℝ) Real.pi, ∀ e : ℝ, 0<e → e≤1 →
      ∀ u : ℝ, 0≤u →
        (∫⁻ ω in diskCenterHit γ G θ e, diskLevelMass κ θ B γ G u K ω ^ m ∂P) ≤
          M*ENNReal.ofReal (e^codimension κ) := by
  obtain ⟨D,hD,hbound⟩ := cappedDistanceKernel_fixed_center_bound m
    (codimension_pos κ hκ8) (by unfold codimension dimension; linarith) b K hK.isBounded
  refine ⟨ENNReal.ofReal (multipointConstant κ (m+1))*D,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD,?_⟩
  intro θ hθ e he he1 u hu
  apply (diskLevelMass_centered_moment_bound hB hm hBm hc h0 hκ hκ8
    γ G F hw hgrowth K hK.measurableSet hKd b hb hb1 hbK θ hθ m e he he1 u hu).trans
  unfold centeredLevelMomentBound
  calc
    _ ≤ ENNReal.ofReal (e^codimension κ)*(ENNReal.ofReal (multipointConstant κ (m+1))*D) := by
      gcongr
      exact hbound 0
    _ = _ := mul_comm _ _

end SLEExactGauge.Multipoint

end

end OAI
