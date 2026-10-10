import OAI.Probability.DilutedSpin.CavityDatumProjection
import OAI.Probability.DilutedSpin.CompoundSample
import OAI.Probability.DilutedSpin.ReservoirInsertionOnEnergy
import OAI.Probability.DilutedSpin.RootSplit

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

noncomputable def energyInsertionFunctional (ρ : Measure E) (F : E → ℝ) (v : E) : ℝ :=
  ∫ E,F (E+v)-F E ∂ρ

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertion_integrable (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    Integrable (fun E => F (E+v)-F E) ρ := by
  apply Integrable.of_bound (hF.continuous.comp (continuous_id.add continuous_const) |>.sub hF.continuous).aestronglyMeasurable ‖v‖
  exact ae_of_all _ (fun E => by simpa using hF.norm_sub_le (E+v) E)

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_lipschitz (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (energyInsertionFunctional ρ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,energyInsertionFunctional]
  rw [← integral_sub (energyInsertion_integrable ρ hF v) (energyInsertion_integrable ρ hF w)]
  apply abs_integral_le_bound
  intro E
  simpa only [sub_sub_sub_cancel_right,add_sub_add_left_eq_sub,NNReal.coe_one,one_mul,
    Real.norm_eq_abs] using hF.norm_sub_le (E+v) (E+w)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_bound (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    |energyInsertionFunctional ρ F v|≤‖v‖ := by
  apply abs_integral_le_bound
  intro E
  simpa only [add_sub_cancel_left,NNReal.coe_one,one_mul,Real.norm_eq_abs] using hF.norm_sub_le (E+v) E

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integral_energyInsertionFunctional (ρ μ : Measure E) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] (hμ : Integrable id μ) {F : E → ℝ} (hF : LipschitzWith 1 F) :
    (∫ v,energyInsertionFunctional ρ F v ∂μ)=∫ E,∫ v,F (E+v)-F E ∂μ ∂ρ := by
  unfold energyInsertionFunctional
  apply integral_integral_swap
  apply (hμ.norm.comp_fst ρ).mono'
    ((hF.continuous.comp (continuous_snd.add continuous_fst)).sub
      (hF.continuous.comp continuous_snd)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simpa only [Function.comp_def,id_eq,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul]
      using hF.norm_sub_le (z.2+z.1) z.2)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

noncomputable def activeCountMean (M : Model p) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) : ℝ :=
  ∫ z,activeDatumRoot T U V x m j f l z ∂rootLaw l (fun _ =>
    M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedDatumRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p × (Fin p → R)) l) :
    |allocatedDatumRoot T U V x m j s f l c z|≤‖f‖+∑ a,‖(rootArray l z a).1.1‖ := by
  apply backwardLog_bound n _ m hm
  intro y
  simpa only [rootArray_rootMap] using allocatedEnergy_bound V x j s l
    (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f (fun w => norm_le_pi_norm f w) y

lemma allocatedDatumRoot_integrable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2)
      ((rootLaw l (fun _ => finiteUniform (Fin N))).prod
        (rootLaw l (fun _ => M.disorder.toMeasure.prod
          ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))) := by
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖)
      (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  apply ((integrable_const ‖f‖).add ((integrable_rootArray_sum _ _ hi l).comp_snd
    (rootLaw l (fun _ => finiteUniform (Fin N))))).mono'
    (measurable_allocatedDatumRoot T U V x m j s f l).aestronglyMeasurable
  exact ae_of_all _ (fun z => allocatedDatumRoot_bound T U V x m hm j s f l z.1 z.2)

lemma upperAllocatedMean (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    (∫ z : RootPath (UpperDatum p N R) l,
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f)
        ∂rootLaw l (fun _ => upperDatumLaw M Q))=
      ∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  let F := fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
    allocatedDatumRoot T U V x m j s f l z.1 z.2
  have hFm := measurable_allocatedDatumRoot T U V x m j s f l
  have he : (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))=
      fun z => F (rootMap Prod.fst l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z),
        rootMap Prod.snd l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z)) := by
    funext z
    simp only [F,allocatedDatumRoot,rootMap_comp,Function.comp_def]
  rw [he]
  apply (integral_rootMap (upperDatum_site_projection M Q j) l
    (fun z => F (rootMap Prod.fst l z,rootMap Prod.snd l z))
    (hFm.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
      (measurable_rootMap Prod.snd measurable_snd l)))).trans
  rw [integral_rootSplit _ _ l F hFm (allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)]
  apply integral_congr_ae
  filter_upwards [] with c
  exact allocatedMean_selected M Q T U V x m j f s l c

end DilutedSpinGlass.PrescribedTree

end

end OAI
