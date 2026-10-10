import OAI.Probability.DilutedSpin.CavityInsertionFunctional
import OAI.Probability.DilutedSpin.CavitySiteMean
import OAI.Probability.DilutedSpin.CompoundRateAverage

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArrayValue_shift [MeasurableSpace X] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) (E : (Fin N → Spin) → ℝ) :
    cavityArrayValue ξ theta field (fun v => F (E+v)-F E) 0 z=
      cavityArrayValue ξ theta field F E z-F E := by
  have h := cavityArray_insertionFunctional (Measure.dirac E) ξ theta field hhm hF hH hC hh z hz
  have he v : energyInsertionFunctional (Measure.dirac E) F v=F (E+v)-F E := by
    unfold energyInsertionFunctional
    rw [integral_dirac]
  simp only [integral_dirac,he] at h
  convert h using 1
  unfold cavityArrayValue cavityArrayEnergy
  congr 1
  ext j
  congr 1
  ext y
  congr 2
  ext σ
  simp

lemma cavityArrayValue_gap_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (z : Fin k → X) (E : (Fin N → Spin) → ℝ) :
    |cavityArrayValue ξ theta field F E z-F E|≤H+C*k := by
  rw [← cavityArrayValue_shift ξ theta field hhm hF hH hC hh z (fun a => hθ _) E]
  have hb : ∀ v,|F (E+v)-F E|≤‖v‖+0 := fun v => by
    simpa using hF.norm_sub_le (E+v) E
  simpa using cavityArrayValue_bound ξ theta field hH hC hθ hh hb 0 z

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

omit [NeZero N] in
lemma liftOldEnergy_lipschitz [NeZero N] : LipschitzWith 1 (liftOldEnergy (N := N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro σ
  exact norm_le_pi_norm (E-F) (fun i => σ i.succ)

lemma averagedEnergyRoot_cavity_rate_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r t s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)|≤
      C*|(r:ℝ)-t|+4*D*s/(N+1) := by
  let G := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
  let μn := Measure.map (newPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin q → Fin N)))
  have hnM := measurable_newPotential (N := N) theta hθm
  have : IsProbabilityMeasure μn := inferInstance
  have hnb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  have hin : Integrable id μn := by
    apply (integrable_map_measure aestronglyMeasurable_id hnM.aemeasurable).mpr
    exact Integrable.of_bound hnM.aestronglyMeasurable C (ae_of_all _ hnb)
  have hni : (∫ v,‖v‖ ∂μn)≤C := by
    rw [show (∫ v,‖v‖ ∂μn)=∫ z,‖newPotential theta z‖ ∂(μ.prod (finiteUniform (Fin q → Fin N))) from
      integral_map hnM.aemeasurable continuous_norm.aestronglyMeasurable]
    exact (le_abs_self _).trans (abs_integral_le_bound (fun z => by simpa only [abs_of_nonneg (norm_nonneg _)] using hnb z))
  have hGl : LipschitzWith 1 G := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    _ m hm field hhm (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)
  have hrate := (integrated_compound_rate_bound μn hin ρ hρ liftOldEnergy_lipschitz hGl r t).trans
    (mul_le_mul_of_nonneg_left hni (abs_nonneg ((r:ℝ)-t)))
  have hr := averagedEnergyRoot_old_new_compare μ ξ ν ρ hρ r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  have ht := averagedEnergyRoot_old_new_compare μ ξ ν ρ hρ t s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  dsimp only [G,μn] at hrate
  have h1 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r μn ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
  have h2 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
    (∫ E,cavityPoissonValue μ ξ theta field
      (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)
  dsimp only [G,μn] at h1 h2
  rw [abs_sub_comm] at hr
  exact (h2.trans (add_le_add (h1.trans (add_le_add hr hrate)) ht)).trans_eq (by ring)

end DilutedSpinGlass

end

end OAI
