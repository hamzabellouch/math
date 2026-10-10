import OAI.Probability.SLE.Geometry.JointRadiusKernel
import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

/-! Spatial Loewner kernels up to a deterministic time depend only on the
driver up to that time. The marked point is kept as a measurable parameter. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma clipped_flow_eqOn_prefix
    {U V : ℝ≥0 → ℝ} {Q R : ℝ → ℂ × ℝ}
    (lo hi : ℝ) (hle : lo ≤ hi) (T : ℝ≥0)
    (hU : ∀ t, t ≤ T → U t = V t)
    (hQ : ∀ t, 0 ≤ t → HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Ici 0) t)
    (hR : ∀ t, 0 ≤ t → HasDerivWithinAt R
      (clippedLogLoewnerField lo hi hle (V t.toNNReal) (R t)) (Ici 0) t)
    (hzero : Q 0 = R 0) : EqOn Q R (Icc 0 (T : ℝ)) := by
  obtain ⟨_, K, _, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun t q => clippedLogLoewnerField lo hi hle (U t.toNNReal) q)
    (s := fun _ => univ) (K := K)
  · intro t _
    exact (hlip _).lipschitzOnWith
  · intro t ht
    exact (hQ t ht.1).continuousWithinAt.mono Icc_subset_Ici_self
  · intro t ht
    exact (hQ t ht.1).mono (Ici_subset_Ici.mpr ht.1)
  · simp
  · intro t ht
    exact (hR t ht.1).continuousWithinAt.mono Icc_subset_Ici_self
  · intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2.le
    rw [hU _ htT]
    exact (hR t ht.1).mono (Ici_subset_Ici.mpr ht.1)
  · simp
  · exact hzero

lemma spatial_clipped_eqOn_prefix
    {Ω : Type*} {m m' : MeasurableSpace Ω} {U V : ℝ≥0 → Ω → ℝ}
    (c : @SpatialClippedFamily Ω m U) (d : @SpatialClippedFamily Ω m' V)
    (T : ℝ≥0) (hUV : ∀ t, t ≤ T → ∀ ω, U t ω = V t ω) :
    ∀ n z ω, EqOn (fun t => (@SpatialClippedFamily.Q Ω m U c) n t (z,ω))
      (fun t => (@SpatialClippedFamily.Q Ω m' V d) n t (z,ω))
      (Icc 0 (T : ℝ)) := by
  intro n z ω
  apply clipped_flow_eqOn_prefix (-(n : ℝ)) n _ T
    (fun t ht => hUV t ht ω) (@SpatialClippedFamily.derivative Ω m U c n z ω)
      (@SpatialClippedFamily.derivative Ω m' V d n z ω)
  rw [@SpatialClippedFamily.initial Ω m U c, @SpatialClippedFamily.initial Ω m' V d]

lemma exists_past_spatial_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (c : SpatialClippedFamily (fun t ω => Real.sqrt κ * B t ω))
    (T : ℝ≥0) :
    ∃ d : @SpatialClippedFamily Ω
        (Filtration.natural B (fun t => (hm t).stronglyMeasurable) T)
        (fun t ω => Real.sqrt κ * B (min t T) ω),
      ∀ n z ω, EqOn (fun t => (@SpatialClippedFamily.Q Ω mΩ _ c) n t (z,ω))
        (fun t => (@SpatialClippedFamily.Q Ω
          (Filtration.natural B (fun t => (hm t).stronglyMeasurable) T) _ d) n t (z,ω))
        (Icc 0 (T : ℝ)) := by
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hf := measurable_driver_frozen B hBm hc T
  let : MeasurableSpace Ω := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
  have hfm : Measurable (fun p : ℝ≥0 × Ω => Real.sqrt κ * B (min p.1 T) p.2) := by
    have h := hf.comp (NNReal.continuous_coe.measurable.prodMap measurable_id)
    have h' := h.const_mul (Real.sqrt κ)
    change Measurable (fun p : ℝ≥0 × Ω =>
      Real.sqrt κ * B (min (p.1 : ℝ).toNNReal T) p.2) at h'
    simpa only [Real.toNNReal_coe] using h'
  let d := spatialClippedFamily (fun t ω => Real.sqrt κ * B (min t T) ω) hfm
    (fun ω => ((hc ω).comp (continuous_id.min continuous_const)).const_mul _)
  refine ⟨d, spatial_clipped_eqOn_prefix c d T ?_⟩
  intro t ht ω
  rw [min_eq_left ht]

/-- All three spatial kernels are jointly measurable in the marked point,
sample, and time restricted to the natural past at `T`. -/
theorem actual_spatial_past_kernels
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (T : ℝ≥0) :
    let mT := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
    @Measurable (Iic T × (ℂ × Ω)) ℝ ((inferInstance : MeasurableSpace (Iic T)).prod
      ((borel ℂ).prod mT)) (borel ℝ)
      (fun p => greenDensity κ (fun t => Real.sqrt κ * B t p.2.2)
        (γ p.2.2) (G p.2.2) p.1 p.2.1) ∧
    @Measurable (Iic T × (ℂ × Ω)) ℝ ((inferInstance : MeasurableSpace (Iic T)).prod
      ((borel ℂ).prod mT)) (borel ℝ)
      (fun p => if p.2.1 ∈ survivingDomain (γ p.2.2) p.1 then
        fullRadius (G p.2.2) p.1 p.2.1 else 0) ∧
    @MeasurableSet (Iic T × (ℂ × Ω)) ((inferInstance : MeasurableSpace (Iic T)).prod
      ((borel ℂ).prod mT)) {p | p.2.1 ∈ survivingDomain (γ p.2.2) p.1} := by
  let c := spatialClippedFamily (fun t ω => Real.sqrt κ * B t ω)
    ((measurable_uncurry_of_continuous_of_measurable hc hm).const_mul _)
    (fun ω => (hc ω).const_mul _)
  obtain ⟨d, hd⟩ := exists_past_spatial_family hm hc κ c T
  have hf := measurable_driver_frozen B
    (measurable_uncurry_of_continuous_of_measurable hc hm) hc T
  let : MeasurableSpace Ω := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
  have hmap : Measurable (fun p : Iic T × (ℂ × Ω) => ((p.1 : ℝ≥0),p.2)) :=
    measurable_subtype_coe.prodMap measurable_id
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B (min p.1 T) p.2) := by
    have h := hf.comp (NNReal.continuous_coe.measurable.prodMap measurable_id)
    change Measurable (fun p : ℝ≥0 × Ω => B (min (p.1 : ℝ).toNNReal T) p.2) at h
    simpa only [Real.toNNReal_coe] using h
  have he (n : ℕ) (p : Iic T × (ℂ × Ω)) :
      (@SpatialClippedFamily.Q Ω mΩ _ c) n (p.1 : ℝ≥0) p.2 = d.Q n (p.1 : ℝ≥0) p.2 :=
    hd n p.2.1 p.2.2 ⟨p.1.val.coe_nonneg, by exact_mod_cast p.1.property⟩
  have hv (n : ℕ) (p : Iic T × (ℂ × Ω)) :
      (@SpatialClippedFamily.valid Ω mΩ _ c) n p.1 p.2.1 p.2.2 ↔ d.valid n p.1 p.2.1 p.2.2 := by
    simp only [SpatialClippedFamily.valid, he]
  have hgreen (p : Iic T × (ℂ × Ω)) :
      d.jointGreen κ (fun t ω => B (min t T) ω) (p.1,p.2) =
      greenDensity κ (fun t => Real.sqrt κ * B t p.2.2)
        (γ p.2.2) (G p.2.2) p.1 p.2.1 := by
    rw [← (@SpatialClippedFamily.jointGreen_eq Ω mΩ _ c) κ B p.2.2 ((hc p.2.2).const_mul _) (fun _ => rfl) (hw p.2.2)]
    unfold SpatialClippedFamily.jointGreen
    congr 1
    funext n
    simp only [SpatialClippedFamily.greenApprox, hv, he,
      min_eq_left (show (p.1 : ℝ≥0) ≤ T from p.1.property)]
  have hradius (p : Iic T × (ℂ × Ω)) : d.jointRadius (p.1,p.2) =
      if p.2.1 ∈ survivingDomain (γ p.2.2) p.1 then
        fullRadius (G p.2.2) p.1 p.2.1 else 0 := by
    rw [← (@SpatialClippedFamily.jointRadius_eq Ω mΩ _ c) p.2.2 ((hc p.2.2).const_mul _) (hw p.2.2)]
    unfold SpatialClippedFamily.jointRadius
    congr 1
    funext n
    simp only [SpatialClippedFamily.radiusApprox, hv, he]
  have hlive (p : Iic T × (ℂ × Ω)) : d.jointLive (p.1,p.2) ↔
      p.2.1 ∈ survivingDomain (γ p.2.2) p.1 := by
    rw [← (@SpatialClippedFamily.jointLive_iff Ω mΩ _ c) p.2.2 ((hc p.2.2).const_mul _) (hw p.2.2)]
    exact exists_congr (fun n => (hv n p).symm)
  refine ⟨?_, ?_, ?_⟩
  · convert ((d.jointGreen_measurable κ (fun t ω => B (min t T) ω) hBm).comp hmap) using 1
    funext p
    exact (hgreen p).symm
  · convert (d.jointRadius_measurable.comp hmap) using 1
    funext p
    exact (hradius p).symm
  · convert d.jointLive_measurable.preimage hmap using 1
    ext p
    exact (hlive p).symm

end SLEExactGauge

end

end OAI
