import OAI.Probability.RadialTransition.MacroLower

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma measurable_countWeight {φ : Potential} (hφ : Continuous φ) (β : ℝ) (F : ℕ → ℝ) :
    Measurable (fun s : ParticleState Position => F (particleCount s)*Real.exp (-β*orderedEnergy φ s.2)) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro n
  change Continuous (fun x : Fin n → Position => F n * Real.exp (-β*orderedEnergy φ x))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_orderedEnergy hφ)))

lemma lintegral_countWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) {A : Set Position} (hAfin : volume A ≠ ⊤) :
    (∫⁻ s : ParticleState Position,
      ENNReal.ofReal (F (particleCount s)*Real.exp (-β*orderedEnergy φ s.2))
      ∂particleBase (volume.restrict A) z) =
    ∑' n : ℕ, ENNReal.ofReal (F n*Real.exp (z*n)*partitionOn φ A n β) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  rw [lintegral_particleBase _ _ (measurable_countWeight hφ β F).ennreal_ofReal]
  apply tsum_congr
  intro n
  dsimp only [particleCount]
  have hi := (integrable_orderedBoltzmann (ι := Fin n) hφ hb β (Measure.pi (fun _ => volume.restrict A))).const_mul (F n)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => mul_nonneg (hF n) (Real.exp_pos _).le)), integral_const_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [partitionOn, rawPartition, div_eq_mul_inv]
  ring

lemma partitionOn_macroRegion (φ : Potential) {q : ℕ} (hq : 0 < q) (i : Cell) (n : ℕ) (β : ℝ) :
    partitionOn φ (macroRegion q i) n β = partition φ ((q:ℝ)/4) n β := by
  rw [macroRegion_translate hq, partitionOn_translate]
  have hh : partitionOn φ (halfCube ((q:ℝ)/4)) n β = partitionOn φ (cube ((q:ℝ)/4)) n β := by
    simp only [partitionOn, rawPartition, restrict_halfCube]
  rw [hh, partitionOn_cube]

section MapWeight
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]

lemma lintegral_pairWeight_map (v : Y → Y → ℝ) (hv : Measurable (Function.uncurry v))
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f) (β z : ℝ) (F : ℕ → ℝ) :
    (∫⁻ s : ParticleState X, ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin (fun x y => v (f x) (f y)) s)) ∂particleBase μ z) =
    ∫⁻ s : ParticleState Y, ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin v s)) ∂particleBase (Measure.map f μ) z := by
  have hfun : Measurable (fun s : ParticleState Y => ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin v s))) := by
    apply Measurable.ennreal_ofReal
    exact (((continuous_of_discreteTopology : Continuous F).comp continuous_particleCount).measurable).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_pairWithin v hv)))
  rw [← particleBase_map μ z hf, lintegral_map hfun (measurable_mapParticle hf)]
  rfl

end MapWeight

lemma lintegral_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∫⁻ s : ParticleState (macroRegion q i), ENNReal.ofReal (F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s))
      ∂particleBase (regionMeasure (macroRegion q i)) z) =
    ∑' n : ℕ, ENNReal.ofReal (F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β) := by
  have hfin : volume (macroRegion q i) ≠ ⊤ := by rw [volume_macroRegion hq]; finiteness
  let : IsFiniteMeasure (regionMeasure (macroRegion q i)) := regionMeasure_finite (measurableSet_macroRegion _ _) hfin
  rw [lintegral_pairWeight_map (radialPair φ) (continuous_radialPair hφ).measurable _ Subtype.val measurable_subtype_coe,
    regionMeasure_map (measurableSet_macroRegion _ _)]
  simp only [pairWithin_radial]
  rw [lintegral_countWeight hφ hb β z F hF hfin]
  simp only [partitionOn_macroRegion φ hq]

lemma integrable_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    Integrable (fun s : ParticleState (macroRegion q i) => F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s))
      (particleBase (regionMeasure (macroRegion q i)) z) := by
  have hm : Measurable (fun s : ParticleState (macroRegion q i) => F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s)) := by
    exact ((continuous_of_discreteTopology.comp continuous_particleCount).measurable).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_pairWithin _
        (continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val).measurable)))
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall (fun s => mul_nonneg (hF _) (Real.exp_pos _).le))).mp
  rw [lintegral_macroWeight hφ hb hq i β z F hF,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)) hs]
  exact ENNReal.ofReal_ne_top

lemma integral_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    (∫ s : ParticleState (macroRegion q i), F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s)
      ∂particleBase (regionMeasure (macroRegion q i)) z) =
      ∑' n, F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun s => mul_nonneg (hF _) (Real.exp_pos _).le))
    (integrable_macroWeight hφ hb hq i β z F hF hs).aestronglyMeasurable,
    lintegral_macroWeight hφ hb hq i β z F hF,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)))]

end RadialTransition

end

end OAI
