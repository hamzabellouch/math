import Mathlib
import OAI.Probability.IsingPerceptron.NamespaceSplit

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma integral_comp_preserving_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have h := integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hF)
  rw [hf.map_eq] at h
  exact h.symm

def enrichedMeanPressure {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) : ℝ :=
  ∫ p, enrichedCylinderPressure n h u ν φ p ∂enrichedCylinderLaw P r n b

def enrichedCGF {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (j : Fin N) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (v : ℝ) (p : EnrichedFrozenData n j A × (ℕ → ℝ)) : ℝ :=
  cgf (fun s => cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2)
    (enrichedFrozenReference n h u j ν φ p.1) (perturbationAmplitude N j*v)

theorem enrichedCGF_integral {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let Q := (enrichedFrozenLaw P r n b j).prod gaussianCoordinates
    MemLp (enrichedCGF n h u j ν φ v) 2 Q ∧
      (∫ z, enrichedCGF n h u j ν φ v z ∂Q) =
      N*(enrichedMeanPressure P r n b h (Function.update u j v) ν φ -
        enrichedMeanPressure P r n b h (Function.update u j 0) ν φ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hv1 := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n))
    (Function.update u j v) (update_abs_le_two hu j hv) ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn.ne'])).1
  have h01 := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n))
    (Function.update u j 0) (update_abs_le_two hu j (by norm_num)) ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn.ne'])).1
  have hp := enrichedInsert_preserving P r n b j
  have hv2 := hv1.comp_measurePreserving hp
  have h02 := h01.comp_measurePreserving hp
  have he := enriched_cgf_eq_pressure_difference hN n b hh h0 u hu j hv ν P hK hφ r
  change enrichedCGF n h u j ν φ v =ᵐ[(enrichedFrozenLaw P r n b j).prod gaussianCoordinates]
    (fun p => N*(enrichedCylinderPressure n h (Function.update u j v) ν φ (enrichedInsert n j p) -
      enrichedCylinderPressure n h (Function.update u j 0) ν φ (enrichedInsert n j p))) at he
  have hL := (hv2.sub h02).const_mul (N:ℝ)
  refine ⟨MemLp.ae_eq he.symm hL, ?_⟩
  rw [integral_congr_ae he, integral_const_mul]
  have hisub := integral_sub (hv2.integrable (by norm_num)) (h02.integrable (by norm_num))
  dsimp only [Function.comp_def] at hisub
  rw [hisub]
  rw [integral_comp_preserving_ae hp hv1.aestronglyMeasurable,
    integral_comp_preserving_ae hp h01.aestronglyMeasurable]
  rfl

theorem enrichedCGF_center_bound {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := (enrichedFrozenLaw P r n b j).prod gaussianCoordinates
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    (∫ z, |enrichedCGF n h u j ν φ v z - ∫ z', enrichedCGF n h u j ν φ v z' ∂Q| ∂Q) ≤
      2*N*Real.sqrt ((C+H+4+5*K^2*α)/N) := by
  let Q := (enrichedFrozenLaw P r n b j).prod gaussianCoordinates
  let F := enrichedCylinderPressure n h (Function.update u j v) ν φ ∘ enrichedInsert n j
  let B := enrichedCylinderPressure n h (Function.update u j 0) ν φ ∘ enrichedInsert n j
  let δ := Real.sqrt ((4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+5*K^2*α)/N)
  have hv1 := enrichedCylinderPressure_field_cap hN n b hb hh h0 hH
    (Function.update u j v) (update_abs_le_two hu j hv) ν P hm hK hφ r hr
  have h01 := enrichedCylinderPressure_field_cap hN n b hb hh h0 hH
    (Function.update u j 0) (update_abs_le_two hu j (by norm_num)) ν P hm hK hφ r hr
  have hp := enrichedInsert_preserving P r n b j
  have hF : MemLp F 2 Q := hv1.1.comp_measurePreserving hp
  have hB : MemLp B 2 Q := h01.1.comp_measurePreserving hp
  have hvF : Var[F;Q] ≤ (4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+5*K^2*α)/N := by
    have ht := variance_map (X := enrichedCylinderPressure n h (Function.update u j v) ν φ)
      (hp.map_eq.symm ▸ hv1.1.aemeasurable) hp.measurable.aemeasurable
    rw [hp.map_eq] at ht
    rw [← ht]
    exact hv1.2
  have hvB : Var[B;Q] ≤ (4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+5*K^2*α)/N := by
    have ht := variance_map (X := enrichedCylinderPressure n h (Function.update u j 0) ν φ)
      (hp.map_eq.symm ▸ h01.1.aemeasurable) hp.measurable.aemeasurable
    rw [hp.map_eq] at ht
    rw [← ht]
    exact h01.2
  have hcF : (∫ z, |F z-∫ z', F z' ∂Q| ∂Q) ≤ δ :=
    (l1_center_le_sqrt_variance hF).trans (Real.sqrt_le_sqrt hvF)
  have hcB : (∫ z, |B z-∫ z', B z' ∂Q| ∂Q) ≤ δ :=
    (l1_center_le_sqrt_variance hB).trans (Real.sqrt_le_sqrt hvB)
  have hc := centered_sub_L1_bound Q (hF.integrable (by norm_num))
    (hB.integrable (by norm_num)) hcF hcB
  have he := enriched_cgf_eq_pressure_difference hN n b hh h0 u hu j hv ν P hK hφ r
  change enrichedCGF n h u j ν φ v =ᵐ[Q] (fun z => N*(F z-B z)) at he
  have hem : (∫ z, enrichedCGF n h u j ν φ v z ∂Q) =
      N*(∫ z, F z-B z ∂Q) := by
    rw [integral_congr_ae he, integral_const_mul]
  change (∫ z, |enrichedCGF n h u j ν φ v z - ∫ z', enrichedCGF n h u j ν φ v z' ∂Q| ∂Q) ≤ _
  rw [hem]
  calc
    _ = (∫ z, (N:ℝ)*|F z-B z-∫ z', F z'-B z' ∂Q| ∂Q) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      change enrichedCGF n h u j ν φ v z = N*(F z-B z) at hz
      rw [hz, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    _ = N*(∫ z, |F z-B z-∫ z', F z'-B z' ∂Q| ∂Q) := integral_const_mul _ _
    _ ≤ N*(δ+δ) := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N)
    _ = _ := by change N*(δ+δ) = 2*N*δ; ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma noise_energy_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      Integrable (fun v => Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1+p.2) H v)) (noiseLeafKernel (I → ℝ) n T) := by
  have hfin := (linearGrowth_noiseCascade_recursion n b hb μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν) H).1
  have hfac := noiseTreeFactor_leafIntegral n b hb μ
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  have htot : ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfin,hfac,htot] with T hf he ht
  simp only [noiseTreeFactor_terminal] at he
  have hx : (∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
      (fun _ p => p.1+p.2) H v)) ∂noiseLeafKernel (I → ℝ) n T) < ∞ := by
    by_contra! hx
    rw [top_le_iff.mp hx, ENNReal.mul_top ht.1.ne'] at he
    exact hf.2.ne he
  constructor
  · exact (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)
  · rw [hasFiniteIntegral_iff_enorm]
    simpa only [Real.enorm_eq_ofReal_abs,abs_of_pos (Real.exp_pos _)] using hx

lemma labeled_energy_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      Integrable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1))
        (labeledSpinReference n ν p.1) := by
  have hp : MeasurePreserving (labeledNoiseJoin (I → ℝ) n)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ))
      (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)) :=
    ⟨measurable_labeledNoiseJoin _ _,labeledNoiseJoin_law _ _ _ _⟩
  have hg := hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good (I → ℝ) n b hb μ)
  have ht : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      0 < noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) ∧
      noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) < ∞ := by
    apply hp.quasiMeasurePreserving.tendsto_ae.eventually (p := fun T =>
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞)
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have hi := hp.quasiMeasurePreserving.tendsto_ae.eventually
    (noise_energy_exp_integrable n b hb μ ν hμ H)
  filter_upwards [hg,ht,hi] with p hg ht hi
  have hm : Measurable (fun v => Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
      (fun _ p => p.1+p.2) H v)) :=
    (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)).exp)
  have hl := integrable_map_measure (μ := labeledLeafLaw n p.1) hm.aestronglyMeasurable
    (measurable_of_countable (labeledNoiseLeaf (I → ℝ) n p)).aemeasurable
  rw [labeledLeafLaw_noiseMap (I → ℝ) n p.1 p.2 hg ht] at hl
  have hf : Integrable (fun γ => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)))
      (labeledLeafLaw n p.1) := by
    apply (hl.mp hi).congr
    exact ae_of_all _ (fun γ => congrArg Real.exp (labeledEnergy_terminal n p.1 p.2 γ (finiteLogIntegral ν) H))
  change Integrable _ (ν.prod (labeledLeafLaw n p.1))
  change Integrable ((fun s : LabeledLeaf n × I => Real.exp (labeledEnergy n p.2 s.1 H s.2)) ∘ Prod.swap) _
  apply integrable_swap_iff.mpr
  apply (integrable_prod_iff (by exact (measurable_of_countable _).aestronglyMeasurable)).mpr
  constructor
  · exact ae_of_all _ (fun _ => Integrable.of_finite)
  · simpa only [Prod.swap_prod_mk, Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),finiteLogIntegral,
      Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)] using hf

 
def cascadeCoordinateLaw (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ)) :
    Measure (LabeledTree n × (ForestVertex n → I → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (I → ℝ))))

instance cascadeCoordinateLaw_probability (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) : IsProbabilityMeasure (cascadeCoordinateLaw n b μ) := by
  unfold cascadeCoordinateLaw; infer_instance

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinates_preserving (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ)) :
    MeasurePreserving (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
      (p.1,markForestOfCoords (I → ℝ) n p.2)) (cascadeCoordinateLaw n b μ)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)) :=
  (MeasurePreserving.id _).prod ⟨measurable_markForestOfCoords _ _,markForestOfCoords_law _ _ _⟩

def cascadeCoordinateEnergy (n : ℕ) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) (s : I × LabeledLeaf n) : ℝ :=
  H s.1+∑ i : Fin n, p.2 (edgeAt n s.2 i) s.1

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinateEnergy_eq (n : ℕ) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) (s : I × LabeledLeaf n) :
    cascadeCoordinateEnergy n H p s = labeledEnergy n (markForestOfCoords (I → ℝ) n p.2) s.2 H s.1 :=
  (labeledEnergy_edge_sum n p.2 s.2 H s.1).symm

lemma cascadeCoordinate_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ p ∂cascadeCoordinateLaw n b μ,
      Integrable (fun s => Real.exp (cascadeCoordinateEnergy n H p s)) (labeledSpinReference n ν p.1) := by
  simpa only [cascadeCoordinateEnergy_eq] using
    (cascadeCoordinates_preserving n b μ).quasiMeasurePreserving.tendsto_ae.eventually
      (labeled_energy_exp_integrable n b hb μ ν hμ H)

lemma cascadeCoordinate_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    Integrable (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
      ∂labeledSpinReference n ν p.1)) (cascadeCoordinateLaw n b μ) ∧
    (∫ p, Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
      ∂labeledSpinReference n ν p.1) ∂cascadeCoordinateLaw n b μ) = energyRecursion n b μ ν H := by
  let hp := (show MeasurePreserving (labeledNoiseJoin (I → ℝ) n)
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ))
    (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)) from
    ⟨measurable_labeledNoiseJoin _ _,labeledNoiseJoin_law _ _ _ _⟩).comp
      (cascadeCoordinates_preserving n b μ)
  have h := cascadeEnergyLog_conditional n b hb μ ν hμ H
  have he := (cascadeCoordinates_preserving n b μ).quasiMeasurePreserving.tendsto_ae.eventually
    (labeledEnergyLog_eq_cascade n b hb μ ν H)
  have he' : (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
      ∂labeledSpinReference n ν p.1)) =ᵐ[cascadeCoordinateLaw n b μ]
      (fun p => cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n
        (p.1,markForestOfCoords (I → ℝ) n p.2))) := by
    filter_upwards [he] with p hp
    simpa only [cascadeCoordinateEnergy_eq,labeledEnergyLog] using hp
  refine ⟨(hp.integrable_comp_of_integrable h.1).congr he'.symm,?_⟩
  rw [integral_congr_ae he']
  exact (integral_comp_preserving_ae hp h.1.aestronglyMeasurable).trans h.2.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cylinder_weighted_variant_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j))
    (c : ι → ℝ) :
    (∑ i, c i • a i).sum (fun _ v => v^2) = (∑ i, c i • b i).sum (fun _ v => v^2) := by
  classical
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,hc]

lemma dual_cylinderField {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    L (fun i => cylinderField (a i) g) =
      cylinderField (∑ i, L (Pi.single i 1) • a i) g := by
  have hv : (fun i => cylinderField (a i) g) =
      ∑ i, cylinderField (a i) g • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv,map_sum,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,cylinderField_smul,smul_eq_mul,mul_comm]

 

lemma cylinder_finite_law_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j)) :
    gaussianCoordinates.map (fun g i => cylinderField (a i) g) =
      gaussianCoordinates.map (fun g i => cylinderField (b i) g) := by
  classical
  have ha : Measurable (fun g i => cylinderField (a i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))
  have hb : Measurable (fun g i => cylinderField (b i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,integral_map ha.aemeasurable (by fun_prop),
    integral_map hb.aemeasurable (by fun_prop)]
  simp only [dual_cylinderField]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    ← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law,cylinderField_law,cylinder_weighted_variant_eq a b hc]

 

theorem cylinder_fields_law_eq {X : Type*}
    (a b : X → ℕ →₀ ℝ) (hc : ∀ x y, cylinderCross (a x) (a y) = cylinderCross (b x) (b y)) :
    gaussianCoordinates.map (fun g x => cylinderField (a x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (b x) g) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))).aemeasurable
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))).aemeasurable).mpr
  intro I
  exact cylinder_finite_law_eq (fun i : I => a i) (fun i : I => b i) (fun i j => hc i j)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def gaussianPair (g : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  ((fun i => g (Nat.pair 0 i)),fun i => g (Nat.pair 1 i))

lemma gaussianPair_preserving : MeasurePreserving gaussianPair gaussianCoordinates
    (gaussianCoordinates.prod gaussianCoordinates) := by
  have hs : MeasurePreserving (gaussianNamespaceSplit 0) gaussianCoordinates
      (gaussianCoordinates.prod (otherNamespacesLaw 0)) :=
    ⟨measurable_gaussianNamespaceSplit 0,gaussianNamespaceSplit_law 0⟩
  have he := measurePreserving_eval_infinitePi
    (fun _ : {k : ℕ // k ≠ 0} => gaussianCoordinates) ⟨1,by decide⟩
  exact ((MeasurePreserving.id gaussianCoordinates).prod he).comp hs

def gaussianSumCoefficients {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) : ℕ →₀ ℝ :=
  ∑ i : Fin 2, tagCoefficients i (Fin.cases (a x) (fun _ => t • b x) i)

lemma gaussianSumCoefficients_field {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) (g : ℕ → ℝ) :
    cylinderField (gaussianSumCoefficients a b t x) g =
      cylinderField (a x) (gaussianPair g).1 + t*cylinderField (b x) (gaussianPair g).2 := by
  unfold gaussianSumCoefficients
  rw [cylinderField_finset_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderField_tag,cylinderField_smul,gaussianPair]

lemma gaussianSumCoefficients_cross {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x y : X) :
    cylinderCross (gaussianSumCoefficients a b t x) (gaussianSumCoefficients a b t y) =
      cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y) := by
  unfold gaussianSumCoefficients
  rw [cylinderCross_tagged_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderCross_smul,pow_two]

 

theorem cylinder_independent_sum_law {X : Type*} (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    (gaussianCoordinates.prod gaussianCoordinates).map
      (fun g x => cylinderField (a x) g.1+t*cylinderField (b x) g.2) =
      gaussianCoordinates.map (fun g x => cylinderField (c x) g) := by
  rw [← gaussianPair_preserving.map_eq,Measure.map_map (by
    apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)) gaussianPair_preserving.measurable]
  have he : (fun g x => cylinderField (a x) (gaussianPair g).1+t*cylinderField (b x) (gaussianPair g).2) =
      (fun g x => cylinderField (gaussianSumCoefficients a b t x) g) := by
    funext g x; exact (gaussianSumCoefficients_field a b t x g).symm
  change gaussianCoordinates.map (fun g x => cylinderField (a x) (gaussianPair g).1+
    t*cylinderField (b x) (gaussianPair g).2) = _
  rw [he]
  exact cylinder_fields_law_eq _ _ (fun x y => (gaussianSumCoefficients_cross a b t x y).trans (hc x y).symm)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma hasDerivAt_mean_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} (ν : Ω → Measure X) (Y : Ω → X → ℝ)
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) P)
    (hd : ∀ t, Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)) P)
    (v : ℝ) :
    HasDerivAt (fun t => ∫ ω, cgf (Y ω) (ν ω) t ∂P)
      (∫ ω, ∫ x, Y ω x ∂(ν ω).tilted (fun x => v*Y ω x) ∂P) v := by
  let D : ℝ → Ω → ℝ := fun t ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)
  let B : Ω → ℝ := fun ω => |D (v-1) ω|+|D (v+1) ω|
  have hderiv : ∀ᵐ ω ∂P, ∀ t : ℝ, HasDerivAt (cgf (Y ω) (ν ω)) (D t ω) t := by
    filter_upwards [he] with ω hω
    intro t
    dsimp [D]
    rw [integral_tilted_mul_self (mem_interior_integrableExpSet_of_all hω t)]
    exact (analyticAt_cgf (mem_interior_integrableExpSet_of_all hω t)).differentiableAt.hasDerivAt
  have hB : Integrable B P := (hd (v-1)).abs.add (hd (v+1)).abs
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (v-1) (v+1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) (hi v)
    (hd v).aestronglyMeasurable (bound := B) ?_ hB ?_).2
  · filter_upwards [he,hderiv] with ω hω hdω
    intro t ht
    have hmono := (convexOn_cgf_of_all_exp hω).monotoneOn_deriv
      (fun x _ => (hdω x).differentiableAt)
    have hlo := hmono (mem_univ _) (mem_univ _) ht.1.le
    have hhi := hmono (mem_univ _) (mem_univ _) ht.2.le
    rw [(hdω (v-1)).deriv,(hdω t).deriv] at hlo
    rw [(hdω t).deriv,(hdω (v+1)).deriv] at hhi
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by dsimp [B]; linarith [neg_abs_le (D (v-1) ω),abs_nonneg (D (v+1) ω)],
      by dsimp [B]; linarith [le_abs_self (D (v+1) ω),abs_nonneg (D (v-1) ω)]⟩
  · filter_upwards [hderiv] with ω hω
    exact fun t _ => hω t

lemma integral_tilted_eq_single_replica {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} {t : ℝ} (he : Integrable (fun x => Real.exp (t*Y x)) ν)
    (hi : Integrable Y (ν.tilted (fun x => t*Y x))) :
    (∫ x, Y x ∂ν.tilted (fun x => t*Y x)) =
      referenceReplicaMean ν (fun x => t*Y x) (fun σ : Fin 1 → X => Y (σ 0)) := by
  rw [referenceReplicaMean_eq_tilted ν _ he]
  let : IsProbabilityMeasure (ν.tilted (fun x => t*Y x)) := isProbabilityMeasure_tilted he
  exact (integral_comp_eval (μ := fun _ : Fin 1 => ν.tilted (fun x => t*Y x)) (i := 0) hi.aestronglyMeasurable).symm

lemma integrable_random_cylinder_tilted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x, cylinderField (a x) z.2
      ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2)) (P.prod gaussianCoordinates) := by
  have hh := integrable_joint_cylinder_insertion (P := P) hν (fun x => t • a x) a
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg t))
    ha (fun _ : Fin 1 → X => (1:ℝ)) (c := 1) (by norm_num) (by intro; norm_num)
  simp only [mul_one,cylinderField_smul] at hh
  apply hh.congr
  filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
  exact (integral_tilted_eq_single_replica (ν z.1) (hz t)
    ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1:ℝ≥0)).integrable (by norm_num))).symm

 

theorem hasDerivAt_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    HasDerivAt (fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates)
      (∫ z : Ω × (ℕ → ℝ), ∫ x, cylinderField (a x) z.2
        ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2) ∂P.prod gaussianCoordinates) t := by
  apply hasDerivAt_mean_cgf (P := P.prod gaussianCoordinates)
    (fun z : Ω × (ℕ → ℝ) => ν z.1) (fun z x => cylinderField (a x) z.2)
  · exact random_cylinder_all_exp_ae (P := P) hν a ha
  · exact integrable_random_cylinder_cgf (P := P) hν a ha
  · exact integrable_random_cylinder_tilted_mean (P := P) hν a ha

lemma cylinder_tilted_mean_eq_energy {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    (∫ z : Ω × (ℕ → ℝ), ∫ x, cylinderField (a x) z.2
      ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2) ∂P.prod gaussianCoordinates) =
      randomReplicaEnergy P ν a t (fun _ : Fin 1 → X => 1) := by
  unfold randomReplicaEnergy
  apply integral_congr_ae
  filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
  simpa only [mul_one] using integral_tilted_eq_single_replica (ν z.1) (hz t)
    ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1:ℝ≥0)).integrable (by norm_num))

 

theorem hasDerivAt_random_cylinder_covariance {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K d : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hdiag : ∀ x, cylinderCross (a x) (a x) = d) (t : ℝ) :
    HasDerivAt (fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates)
      (t*(d-randomReplicaAverage P ν a t (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))) t := by
  have hd := hasDerivAt_random_cylinder_cgf (P := P) hν a ha t
  rw [cylinder_tilted_mean_eq_energy hν a ha t,
    randomReplicaEnergy_identity hν a ha hdiag t (fun _ : Fin 1 → X => (1:ℝ)) (c := 1)
      (by norm_num) (by intro; norm_num)] at hd
  simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero,one_mul,Nat.reduceAdd,Nat.cast_one,
    Fin.tail,Fin.succ_zero_eq_one] at hd
  rw [randomReplicaAverage_const hν a ha,randomReplicaAverage_const hν a ha] at hd
  simpa only [mul_one,add_zero,Nat.reduceAdd,Nat.cast_one,one_mul,Fin.tail,Fin.succ_zero_eq_one] using hd

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exp_mul_le_endpoints {v t y : ℝ} (ht : t ∈ Icc (v-1) (v+1)) :
    Real.exp (t*y) ≤ Real.exp ((v-1)*y)+Real.exp ((v+1)*y) := by
  by_cases hy : 0 ≤ y
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2 hy)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ht.1 (le_of_not_ge hy))).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

lemma continuous_bounded_exponential_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {Y D : X → ℝ} (hY : Measurable Y) (hD : Measurable D)
    (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν)
    {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ x, |D x| ≤ C) :
    Continuous (fun t : ℝ => ∫ x, Real.exp (t*Y x)*D x ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated (bound := fun x =>
    (Real.exp ((v-1)*Y x)+Real.exp ((v+1)*Y x))*C)
  · exact Eventually.of_forall (fun t => ((hY.const_mul t).exp.mul hD).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhds (show v-1 < v by linarith) (show v < v+1 by linarith)] with t ht
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (exp_mul_le_endpoints ⟨ht.1.le,ht.2.le⟩) (hb x) (abs_nonneg _) (by positivity)
  · exact ((he (v-1)).add (he (v+1))).mul_const C
  · exact ae_of_all _ (fun x => by fun_prop)

lemma replica_all_exp {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν) (r : ℕ) (t : ℝ) :
    Integrable (fun σ : Fin r → X => Real.exp (t*∑ i, Y (σ i))) (Measure.pi (fun _ => ν)) := by
  simpa only [Finset.mul_sum,Real.exp_sum] using
    Integrable.fintype_prod (μ := fun _ : Fin r => ν) (fun _ : Fin r => he t)

lemma continuous_referenceReplicaMean {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hD : ∀ σ, |D σ| ≤ C) :
    Continuous (fun t : ℝ => referenceReplicaMean ν (fun x => t*Y x) D) := by
  have hnum := continuous_bounded_exponential_integral (Measure.pi (fun _ : Fin r => ν))
    (measurable_of_countable (fun σ : Fin r → X => ∑ i, Y (σ i))) (measurable_of_countable D)
    (replica_all_exp ν he r) hC hD
  have hden : Continuous (fun t : ℝ => ∫ x, Real.exp (t*Y x) ∂ν) := by
    simpa only [mul_one] using continuous_bounded_exponential_integral ν
      (measurable_of_countable Y) (measurable_const : Measurable (fun _ : X => (1:ℝ)))
      he (C := 1) (by norm_num) (by intro; norm_num)
  convert hnum.div (hden.pow r) (fun t => pow_ne_zero r (MeasureTheory.integral_exp_pos (he t)).ne') using 1
  funext t
  simp [referenceReplicaMean,referencePartition,Finset.mul_sum]

 

lemma continuous_randomReplicaAverage {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hD : ∀ σ, |D σ| ≤ C) :
    Continuous (fun t : ℝ => randomReplicaAverage P ν a t D) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated (bound := fun _ : Ω × (ℕ → ℝ) => C)
  · filter_upwards [] with t
    exact (integrable_random_scaled_mean (P := P) hν a t D hC hD).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using referenceReplicaMean_abs_le (ν z.1) _ D
        (measurable_of_countable D) hC hD))
  · exact integrable_const _
  · filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
    exact (continuous_referenceReplicaMean (ν z.1) hz D hC hD).continuousAt

end IsingPerceptron

end

end OAI
