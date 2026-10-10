import OAI.Geometry.RCD.Transport.OptimalTripletCompletion
import OAI.Geometry.RCD.Heat.CompactHeatLimitOptimalTriplets
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # The actual interpolation limit agrees with every compressed optimal plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem interpolation_limit_eq_compressed_plan (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ) (hi : StrictMono i) (Q : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (i k)) t) atTop (𝓝 Q))
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hQ : (Q : Measure X) ≤ B • hausdorff n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hpπ : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {F : ℝ≥0∞} (hF : F ≠ ∞) (hcπ : ∀ s : Time, π.map (fun γ => γ s) ≤ F • hausdorff n X) :
    (Q : Measure X)=π.map (fun γ => γ ⟨t,t.property.1.le,t.property.2.le⟩) := by
  obtain ⟨P,j,hj,hP,hPQ,hopt,hgeo,hbounded⟩ := D.interpolation_limit_optimal_triplets
    a₀ b₀ hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT t i hi Q hweak
  obtain ⟨hl,hr⟩ := D.joint_limit_endpoint_marginals t (i ∘ j) P hP
  let a : X × (S × T) → X := fun z => z.2.1
  let b : X × (S × T) → X := fun z => z.2.2
  have ha : Measurable a := measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)
  have hb : Measurable b := measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hma : (P : Measure (X × (S × T))).map a=μ.map Subtype.val := by
    rw [← hl,ProbabilityMeasure.toMeasure_map,
      Measure.map_map measurable_subtype_coe measurable_fst,
      Measure.map_map (measurable_subtype_coe.comp measurable_fst) measurable_snd]
    rfl
  have hmb : (P : Measure (X × (S × T))).map b=ν.map Subtype.val := by
    rw [← hr,ProbabilityMeasure.toMeasure_map,
      Measure.map_map measurable_subtype_coe measurable_snd,
      Measure.map_map (measurable_subtype_coe.comp measurable_snd) measurable_snd]
    rfl
  have hmx : (P : Measure (X × (S × T))).map Prod.fst=(Q : Measure X) :=
    congrArg ProbabilityMeasure.toMeasure hPQ
  have hopt' : IsOptimalCoupling ((P : Measure (X × (S × T))).map a)
      ((P : Measure (X × (S × T))).map b)
      ((P : Measure (X × (S × T))).map (fun z => (a z,b z))) := by
    rw [hma,hmb]
    simpa only [ProbabilityMeasure.toMeasure_map,
      Measure.map_map (measurable_subtype_coe.prodMap measurable_subtype_coe) measurable_snd,
      Function.comp_def,Prod.map,a,b] using hopt
  let C : ℝ≥0∞ := B+(C₀:ℝ≥0∞)+(C₁:ℝ≥0∞)
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨hB,ENNReal.coe_ne_top⟩,ENNReal.coe_ne_top⟩
  have hBC : B ≤ C := le_self_add.trans le_self_add
  have h0C : (C₀:ℝ≥0∞) ≤ C := le_add_self.trans le_self_add
  have h1C : (C₁:ℝ≥0∞) ≤ C := le_add_self
  have hcx : (P : Measure (X × (S × T))).map Prod.fst ≤ C • hausdorff n X := by
    rw [hmx]
    exact hQ.trans (by intro U; exact mul_le_mul' hBC le_rfl)
  have hca : (P : Measure (X × (S × T))).map a ≤ C • hausdorff n X := by
    rw [hma,hμ,← withDensity_const]
    apply withDensity_mono
    filter_upwards [hC₀] with x hx
    exact (ENNReal.ofReal_le_coe.mpr ((le_abs_self _).trans hx)).trans h0C
  have hcb : (P : Measure (X × (S × T))).map b ≤ C • hausdorff n X := by
    rw [hmb,hν,← withDensity_const]
    apply withDensity_mono
    filter_upwards [hC₁] with x hx
    exact (ENNReal.ofReal_le_coe.mpr ((le_abs_self _).trans hx)).trans h1C
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hsa : ∀ᵐ y ∂μ.map Subtype.val, dist y p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hS y
  have hsb : ∀ᵐ y ∂ν.map Subtype.val, dist y p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hT y
  obtain ⟨τ,hτ,hgτ,hpτ,heτ,hcτ⟩ := hX.complete_optimal_triplets hn (P : Measure (X × (S × T)))
    Prod.fst a b measurable_fst ha hb t hopt' hgeo hC hcx hca hcb p (R := 3*R)
    (mul_nonneg (by norm_num) hR0)
    (by rwa [hmx])
    (by rw [hma]; exact hsa.mono fun y hy => hy.trans (by linarith))
    (by rw [hmb]; exact hsb.mono fun y hy => hy.trans (by linarith))
  let := hτ
  rw [hma,hmb] at hpτ
  rw [hmx] at heτ
  have he := hX.compressed_plan_unique_finite hn p hR0 τ π hgτ hgπ hpτ hpπ
    (compressionBudget_ne_top K n (2*(3*R)) hC) hF hcτ hcπ hsa hsb
  rw [he] at heτ
  exact heτ.symm

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
