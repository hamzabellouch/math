import OAI.Probability.SLE.Multipoint.MultipointCenteredWeights
import OAI.Probability.SLE.Multipoint.MultipointFixedCenterKernel

namespace OAI

/-! Integrating the actual multipoint bound on an interior compact set.
The bound is independent of the common radius level. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma ae_tuple_mem {ι : Type*} [Fintype ι] (K : Set ℂ) (hK : MeasurableSet K) :
    ∀ᵐ z : ι → ℂ ∂Measure.pi (fun _ : ι => volume.restrict K), ∀ i, z i ∈ K := by
  apply ae_all_iff.mpr
  intro i
  exact MeasureTheory.Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hK)

lemma compact_positive_radius_cap {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlane) : ∃ b : ℝ, 0 < b ∧ ∀ z ∈ K, b ≤ 2*z.im := by
  exact hK.exists_forall_le' (by fun_prop) (fun z hz => mul_pos (by norm_num) (hKH hz))

def compactLevelMomentBound (κ b : ℝ) (K : Set ℂ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (multipointConstant κ m) *
    ∫⁻ z : Fin m → ℂ, cappedDistanceKernel (codimension κ) b z
      ∂Measure.pi (fun _ : Fin m => volume.restrict K)

theorem levelMass_moment_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im) (m : ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ ω, levelMass κ B γ G u K ω ^ m ∂P) ≤ compactLevelMomentBound κ b K m := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [levelMass_moment_identity P hm hBc κ u hu γ G F hw K m]
  unfold compactLevelMomentBound
  rw [← lintegral_const_mul _ (measurable_cappedDistanceKernel _ _)]
  apply lintegral_mono_ae
  filter_upwards [ae_tuple_mem (ι := Fin m) K hK,ae_tuple_injective (ι := Fin m) K] with z hz hzi
  have h := stoppedGreen_common_level_product_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth z (fun i => hKH (hz i)) hzi (cappedDistance b z)
    (fun i => cap_pos hb hzi i)
    (fun i => (cap_le_fixed b z i).trans (hbR (z i) (hz i)))
    (fun i j hij => cap_le_dist b z i j hij) u
  apply h.trans_eq
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · simp only [multipointConstant,Fintype.card_fin]
  · exact ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (cap_pos hb hzi i).le _)

lemma compactLevelMomentBound_lt_top {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (b : ℝ) (K : Set ℂ) (hK : Bornology.IsBounded K) (m : ℕ) :
    compactLevelMomentBound κ b K m < ⊤ := by
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  exact cappedDistanceKernel_integral_lt_top (codimension_pos κ hκ8)
    (by unfold codimension dimension; linarith) b K hK

theorem uniform_levelMass_compact_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) (m : ℕ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ u : ℝ, 0 ≤ u →
      (∫⁻ ω, levelMass κ B γ G u K ω ^ m ∂P) ≤ M := by
  obtain ⟨b,hb,hbR⟩ := compact_positive_radius_cap hK hKH
  exact ⟨compactLevelMomentBound κ b K m,
    compactLevelMomentBound_lt_top hκ hκ8 b K hK.isBounded m,
    fun u hu => levelMass_moment_le_cappedKernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw
      hgrowth K hK.measurableSet hKH b hb hbR m u hu⟩

theorem uniform_levelApproximation_compact_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) (m : ℕ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ u : ℝ, 0 ≤ u → ∀ t : ℝ≥0∞,
      (∫⁻ ω, (levelApproximation κ B γ G u t ω K) ^ m ∂P) ≤ M := by
  obtain ⟨M,hM,hu⟩ := uniform_levelMass_compact_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH m
  refine ⟨M,hM,fun u hu₀ t => ?_⟩
  apply le_trans (lintegral_mono (fun ω => ?_)) (hu u hu₀)
  exact pow_le_pow_left' (levelApproximation_apply_le κ B γ G u t ω hK.measurableSet) m

def centeredLevelMomentBound (κ b : ℝ) (z₀ : ℂ) (K : Set ℂ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (multipointConstant κ (m+1)) *
    ∫⁻ z : Fin m → ℂ, cappedDistanceKernel (codimension κ) b (Fin.cons z₀ z)
      ∂Measure.pi (fun _ : Fin m => volume.restrict K)

theorem levelMass_centered_moment_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (z₀ : ℂ) (hz₀ : z₀ ∈ upperHalfPlane) (e₀ : ℝ) (he₀ : 0 < e₀) (heR : e₀ ≤ 2*z₀.im)
    (b : ℝ) (hb : 0 < b) (hb₀ : b ≤ 2*z₀.im) (hbR : ∀ z ∈ K, b ≤ 2*z.im) (m : ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ ω in {ω | ∃ t : ℝ≥0, z₀ ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius (fun z : ℂ => z) (G ω) t z₀ ≤ e₀},
      levelMass κ B γ G u K ω ^ m ∂P) ≤
      ENNReal.ofReal (e₀^(codimension κ)) * centeredLevelMomentBound κ b z₀ K m := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let E := {ω | ∃ t : ℝ≥0, z₀ ∈ survivingDomain (γ ω) t ∧
    physicalConformalRadius (fun z : ℂ => z) (G ω) t z₀ ≤ e₀}
  have hE : MeasurableSet E := measurableSet_physical_radius_hit hm hBc κ γ G F hw z₀ hz₀ e₀ he₀ heR
  rw [levelMass_moment_identity (P.restrict E) hm hBc κ u hu γ G F hw K m]
  have hbound : (∫⁻ z : Fin m → ℂ, ∫⁻ ω in E,
      ENNReal.ofReal (∏ i, stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
        (γ ω) (G ω) (z i) u) ∂P ∂Measure.pi (fun _ : Fin m => volume.restrict K)) ≤
      (ENNReal.ofReal (multipointConstant κ (m+1)) * ENNReal.ofReal (e₀^codimension κ)) *
        ∫⁻ z : Fin m → ℂ, cappedDistanceKernel (codimension κ) b (Fin.cons z₀ z)
          ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
    have hc : Measurable (fun z : Fin m → ℂ => (Fin.cons z₀ z : Fin (m+1) → ℂ)) := by
      apply Measurable.of_eval
      intro i
      exact Fin.cases measurable_const (fun j => measurable_pi_apply j) i
    have hk : Measurable (fun z : Fin m → ℂ => cappedDistanceKernel (codimension κ) b
        (Fin.cons z₀ z)) := by
      simpa only [Function.comp_def] using
        (measurable_cappedDistanceKernel (codimension κ) b).comp hc
    rw [← lintegral_const_mul _ hk]
    apply lintegral_mono_ae
    filter_upwards [ae_tuple_mem (ι := Fin m) K hK,ae_tuple_injective (ι := Fin m) K,
      ae_tuple_avoids (ι := Fin m) K z₀] with z hz hzi havoid
    let z' : Fin (m+1) → ℂ := Fin.cons z₀ z
    have hz' : ∀ i, z' i ∈ upperHalfPlane := Fin.cases hz₀ (fun i => hKH (hz i))
    have hzi' : Function.Injective z' := Fin.cons_injective_of_injective
      (by rintro ⟨i,hi⟩; exact havoid i hi) hzi
    have hbR' : ∀ i, b ≤ 2*(z' i).im := Fin.cases hb₀ (fun i => hbR (z i) (hz i))
    have h := stoppedGreen_centered_common_level_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw
      hgrowth m z' hz' hzi' (cappedDistance b z') (fun i => cap_pos hb hzi' i)
      (fun i => (cap_le_fixed b z' i).trans (hbR' i))
      (fun i j hij => cap_le_dist b z' i j hij) e₀ he₀ u
    rw [← lintegral_indicator hE]
    apply h.trans_eq
    rw [ENNReal.ofReal_mul (mul_nonneg (multipointConstant_pos κ _).le
        (Real.rpow_nonneg he₀.le _)),
      ENNReal.ofReal_mul (multipointConstant_pos κ _).le]
    congr 1
    exact ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (cap_pos hb hzi' i).le _)
  exact hbound.trans_eq (by unfold centeredLevelMomentBound; ring)

theorem uniform_levelMass_centered_compact_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im) (m : ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z₀ : ℂ, z₀ ∈ upperHalfPlane → b ≤ 2*z₀.im →
      ∀ e₀ : ℝ, 0 < e₀ → e₀ ≤ 2*z₀.im → ∀ u : ℝ, 0 ≤ u →
        (∫⁻ ω in {ω | ∃ t : ℝ≥0, z₀ ∈ survivingDomain (γ ω) t ∧
          physicalConformalRadius (fun z : ℂ => z) (G ω) t z₀ ≤ e₀},
          levelMass κ B γ G u K ω ^ m ∂P) ≤ C * ENNReal.ofReal (e₀^codimension κ) := by
  obtain ⟨D,hD,hbound⟩ := cappedDistanceKernel_fixed_center_bound m
    (codimension_pos κ hκ8) (by unfold codimension dimension; linarith) b K hK.isBounded
  refine ⟨ENNReal.ofReal (multipointConstant κ (m+1)) * D,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD,?_⟩
  intro z₀ hz₀ hb₀ e₀ he₀ heR u hu
  apply (levelMass_centered_moment_le_cappedKernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth K hK.measurableSet hKH z₀ hz₀ e₀ he₀ heR b hb hb₀ hbR m u hu).trans
  unfold centeredLevelMomentBound
  calc
    _ ≤ ENNReal.ofReal (e₀^codimension κ) *
        (ENNReal.ofReal (multipointConstant κ (m+1)) * D) := by gcongr; exact hbound z₀
    _ = _ := mul_comm _ _

end SLEExactGauge.Multipoint

end

end OAI
