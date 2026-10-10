import OAI.Probability.RadialTransition.OccupationMoments

namespace OAI

universe uX uY

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev ParticleState (X : Type uX) := Σ n : ℕ, Fin n → X

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
instance : MeasurableSpace (ParticleState X) := borel (ParticleState X)
instance : BorelSpace (ParticleState X) := ⟨rfl⟩

def particleCount (x : ParticleState X) : ℕ := x.1

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem continuous_particleCount : Continuous (particleCount (X := X)) :=
  continuous_sigma (fun _ => continuous_const)

theorem measurable_particle_mk (n : ℕ) : Measurable (@Sigma.mk ℕ (fun n => Fin n → X) n) :=
  continuous_sigmaMk.measurable

theorem measurable_particle_iff {Y : Type uY} [MeasurableSpace Y] {f : ParticleState X → Y} :
    Measurable f ↔ ∀ n, Measurable (fun x : Fin n → X => f ⟨n,x⟩) := by
  constructor
  · intro hf n
    exact hf.comp (measurable_particle_mk n)
  · intro hf s hs
    have he : f ⁻¹' s = ⋃ n : ℕ, Sigma.mk n '' ((fun x : Fin n → X => f ⟨n,x⟩) ⁻¹' s) := by
      exact (iUnion_image_preimage_sigma_mk_eq_self (f ⁻¹' s)).symm
    rw [he]
    apply MeasurableSet.iUnion
    intro n
    exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image.mpr (hf n hs)

def particleBase (ν : Measure X) (z : ℝ) : Measure (ParticleState X) :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (Real.exp (z*n) / n.factorial) •
    Measure.map (Sigma.mk n) (Measure.pi (fun _ : Fin n => ν)))

theorem lintegral_particleBase (ν : Measure X) (z : ℝ) {f : ParticleState X → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂particleBase ν z) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (z*n) / n.factorial) *
        ∫⁻ x : Fin n → X, f ⟨n,x⟩ ∂Measure.pi (fun _ => ν) := by
  rw [particleBase, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_map hf (measurable_particle_mk n)]
  rfl

theorem particleBase_univ {ν : Measure X} (hA : ν univ ≠ ⊤) (z : ℝ) :
    particleBase ν z univ = ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp z)) := by
  let : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hA⟩
  have hV : 0 ≤ (ν univ).toReal := ENNReal.toReal_nonneg
  have hf (n : ℕ) : 0 ≤ ((ν univ).toReal * Real.exp z)^n / n.factorial := by positivity
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (z*n) / n.factorial) * (ν univ)^n =
      ENNReal.ofReal (((ν univ).toReal * Real.exp z)^n / n.factorial) := by
    rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_pow hV,
      ← ENNReal.ofReal_mul (by positivity), mul_pow, ← Real.exp_nat_mul]
    simp only [ENNReal.toReal_ofReal hV]
    congr 1
    rw [mul_comm z (n : ℝ)]
    ring
  have hh := lintegral_particleBase ν z (f := fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.pi_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hh
  rw [hh]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf (Real.summable_pow_div_factorial _)]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

instance particleBase_finite {ν : Measure X} (z : ℝ) [IsFiniteMeasure (ν)] :
    IsFiniteMeasure (particleBase ν z) := by
  constructor
  rw [particleBase_univ (measure_ne_top ν univ)]
  exact ENNReal.ofReal_lt_top

def particleVacuum : ParticleState X := ⟨0, Fin.elim0⟩

theorem dirac_vacuum_le_particleBase (ν : Measure X) (z : ℝ) [SigmaFinite ν] :
    Measure.dirac (particleVacuum (X := X)) ≤ particleBase ν z := by
  have hh := Measure.le_sum (fun n : ℕ => ENNReal.ofReal (Real.exp (z*n) / n.factorial) •
    Measure.map (Sigma.mk n) (Measure.pi (fun _ : Fin n => ν))) 0
  rw [Measure.pi_of_empty _ Fin.elim0, Measure.map_dirac' (measurable_particle_mk 0)] at hh
  simpa [particleBase, particleVacuum] using hh

theorem lintegral_exp_particleCount (ν : Measure X) [IsFiniteMeasure ν] (z c : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * particleCount x)) ∂particleBase ν z) =
      ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+c))) := by
  have hf : Measurable (fun x : ParticleState X => ENNReal.ofReal (Real.exp (c * particleCount x))) :=
    (Real.measurable_exp.comp (measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (n : ℝ))).comp continuous_particleCount).measurable)).ennreal_ofReal
  rw [lintegral_particleBase ν z hf, ← particleBase_univ (measure_ne_top ν univ) (z+c)]
  have hh := lintegral_particleBase ν (z+c) (f := fun _ => 1) measurable_const
  rw [show particleBase ν (z+c) univ = ∫⁻ _, (1 : ℝ≥0∞) ∂particleBase ν (z+c) by simp, hh]
  apply tsum_congr
  intro n
  simp only [particleCount, lintegral_const, Measure.pi_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [add_mul, Real.exp_add]
  ring

theorem integrable_exp_particleCount (ν : Measure X) [IsFiniteMeasure ν] (z c : ℝ) :
    Integrable (fun x => Real.exp (c * particleCount x)) (particleBase ν z) := by
  have hf : Measurable (fun x : ParticleState X => Real.exp (c * particleCount x)) :=
    Real.measurable_exp.comp (measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (n : ℝ))).comp continuous_particleCount).measurable)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  rw [lintegral_exp_particleCount]
  exact ENNReal.ofReal_lt_top

end RadialTransition

end

end OAI
