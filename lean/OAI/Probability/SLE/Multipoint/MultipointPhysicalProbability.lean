import OAI.Probability.SLE.Multipoint.MultipointActualProbability
import OAI.Probability.SLE.Multipoint.MultipointPhysicalHits
import OAI.Probability.SLE.Multipoint.MultipointBudgetMonotone

namespace OAI

/-! Physical-domain multipoint approach bounds, including arbitrary
positive targets through the paper's capped product. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

theorem physical_radius_multipoint_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (R b e : ι → ℝ) (he : ∀ i, 0 < e i) (heb : ∀ i, e i ≤ b i)
    (hbR : ∀ i, b i ≤ R i) (hRdef : ∀ i, R i = 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j))) :
    P {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius J (G ω) t (z i) ≤ e i} ≤
      ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)) *
        ∏ i, (e i/b i)^(1-κ/8)) := by
  have heq : {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius J (G ω) t (z i) ≤ e i} =
      {ω | ∀ i, radiusLevelTime (γ ω) (G ω) (z i) (Real.log (R i/e i)) < ⊤} := by
    ext ω
    apply forall_congr'
    intro i
    exact physical_radius_hit_iff_finite_level (continuous_const.mul (hBc ω)) (hw ω)
      J (z i) (R i) (e i) ((he i).trans_le ((heb i).trans (hbR i))) (he i)
      ((heb i).trans (hbR i)) (hRdef i)
  rw [heq]
  exact actual_radius_multipoint_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth J
    hJ hJinj z hz hne R b e he heb hbR hRdef hsep

theorem capped_physical_radius_multipoint_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (R b e : ι → ℝ) (he : ∀ i, 0 < e i) (hb : ∀ i, 0 < b i)
    (hbR : ∀ i, b i ≤ R i) (hRdef : ∀ i, R i = 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j))) :
    P {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius J (G ω) t (z i) ≤ e i} ≤
      ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)) *
        ∏ i, min 1 ((e i/b i)^(1-κ/8))) := by
  classical
  let I := Finset.univ.filter (fun i => e i ≤ b i)
  let f : I ↪ ι := Function.Embedding.subtype _
  have himage : (Finset.univ : Finset I).map f = I := by
    ext i
    simp only [Finset.mem_map,Finset.mem_univ,true_and]
    exact ⟨fun ⟨j,hj⟩ => hj ▸ j.property,fun hi => ⟨⟨i,hi⟩,rfl⟩⟩
  have hsmall := physical_radius_multipoint_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth J hJ hJinj (fun i : I => z i) (fun i => hz i)
    (fun i j hij => Subtype.ext (hne hij)) (fun i : I => R i) (fun i : I => b i)
    (fun i : I => e i) (fun i => he i) (fun i => (Finset.mem_filter.mp i.property).2)
    (fun i => hbR i) (fun i => hRdef i)
    (fun i j hij => hsep i j (fun h => hij (Subtype.ext h)))
  have hsub : {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius J (G ω) t (z i) ≤ e i} ⊆
      {ω | ∀ i : I, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius J (G ω) t (z i) ≤ e i} := fun _ h i => h i
  apply (measure_mono hsub).trans (hsmall.trans (ENNReal.ofReal_le_ofReal ?_))
  have hK : uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset I) ≤
      uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι) := by
    rw [← uniformDiscountBudget_map κ (sourceBeta κ) f,himage]
    exact uniformDiscountBudget_mono hκ hκ8 (Finset.subset_univ I)
  have hcard : Fintype.card I ≤ Fintype.card ι := by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_le_card (Finset.subset_univ I)
  have hα : 0 ≤ 1-κ/8 := by linarith
  have hprod : (∏ i : I, (e i/b i)^(1-κ/8)) = ∏ i, min 1 ((e i/b i)^(1-κ/8)) := by
    rw [Finset.prod_coe_sort I (fun i : ι => (e i/b i)^(1-κ/8))]
    dsimp only [I]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : e i ≤ b i
    · rw [ite_eq_left hi,min_eq_right (Real.rpow_le_one (div_nonneg (he i).le (hb i).le)
        ((div_le_one (hb i)).mpr hi) hα)]
    · rw [ite_eq_right hi,min_eq_left (Real.one_le_rpow
        ((one_le_div (hb i)).mpr (le_of_not_ge hi)) hα)]
  rw [← hprod]
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun (i : I) _ => Real.rpow_nonneg
    (div_nonneg (he i).le (hb i).le) _))
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hcard)
    (Real.exp_le_exp.mpr hK) (Real.exp_pos _).le (by positivity)

end SLEExactGauge.Multipoint

end

end OAI
