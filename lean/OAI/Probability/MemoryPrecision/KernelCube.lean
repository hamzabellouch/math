import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelCaps
import OAI.Probability.MemoryPrecision.KernelIntegral
import OAI.Probability.MemoryPrecision.KernelVersion
import OAI.Probability.MemoryPrecision.SeedAverage
import OAI.Probability.MemoryPrecision.StochasticMass

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression

def CubePrior {d : ℕ} (hd : 2 ≤ d) : Measure (MemoryPrecision.Kernel.Sphere d) :=
  (CubeLaw d).map (CubeSphere hd)
instance {d : ℕ} (hd : 2 ≤ d) : IsProbabilityMeasure (CubePrior hd) := by
  unfold CubePrior
  infer_instance

lemma cubeSphere_preserving {d : ℕ} (hd : 2 ≤ d) :
    MeasurePreserving (CubeSphere hd) (CubeLaw d) (CubePrior hd) :=
  ⟨cubeSphere_measurable hd, rfl⟩

namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma eval_comp {X Y : Type*} (w : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞) (ι : Y → X)
    (n k : ℕ) (j : MemoryPrecision.Kernel.State M) (s : Y) (obs : Observations d k) :
    K.eval w n k j (ι s) obs = K.eval (fun n j s => w n j (ι s)) n k j s obs := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    simp only [eval]
    apply Finset.sum_congr rfl
    intro a _
    rw [ih]
lemma pathValue_comp {X Y : Type*} (w : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞) (ι : Y → X)
    (s : Y) (obs : Observations d T) :
    K.pathValue w (ι s) obs = K.pathValue (fun n j s => w n j (ι s)) s obs := by
  simp only [pathValue, K.eval_comp w ι]

lemma borel_cube_bound (hK : K.Borel) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Cube d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) (CubeSphere (d := d) (by omega) z.1)
        (records (CubeSphere (d := d) (by omega) z.1) z.2)
      ∂(CubeLaw d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have hm₁ : Measurable (fun z : Cube d × Rows d T =>
      (CubeSphere (d := d) (by omega) z.1,z.2)) :=
    ((cubeSphere_measurable (d := d) (by omega)).comp measurable_fst).prodMk measurable_snd
  have hm₀ := K.experiment_fixed_measurable (f := chordTest (d := d) ε) hK (measurable_chordTest ε)
  have hm := hm₀.comp hm₁
  have hprod := lintegral_prod (μ := CubeLaw d) (ν := RowLaw d T) _ hm.aemeasurable
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  simp_rw [K.pathValue_comp _ (CubeSphere (d := d) (by omega))]
  apply K.integral_pathValue_bound (fun n j u => K.outputTest (chordTest ε) n j (CubeSphere (d := d) (by omega) u))
    (CubeEmbedding d) hK
    (fun n j => (K.outputTest_measurable (measurable_chordTest ε) n j).comp (cubeSphere_measurable (d := d) (by omega)))
    (cubeEmbedding_measurable d) (CubeLaw d)
  intro r hr j
  apply cube_mass_bound
  exact stoch_cube_mass hd (show 1 ≤ 2^M from one_le_pow₀ (by norm_num))
    (K.marginal_measurable hK) (fun n j obs => (K.marginal_sum n j obs).le)
    (fun n j => (K.outputTest_measurable (measurable_chordTest ε) n j).comp (cubeSphere_measurable (d := d) (by omega)))
    (fun n j u => K.outputTest_le_one (chordTest_le_one ε) n j (CubeSphere (d := d) (by omega) u))
    (by positivity) (K.output_chord_cube_local (by omega) hε)
    (MemoryPrecision.BlockCount T ((d/2)/4)) r
    (hr.trans (blockCount_mul_ge T (by omega))) 0 j

lemma completed_cube_bound (hK : K.Completed) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Cube d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) (CubeSphere (d := d) (by omega) z.1)
        (records (CubeSphere (d := d) (by omega) z.1) z.2)
      ∂(CubeLaw d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have he := K.version_pathValue_ae ((CubeLaw d).prod (RowLaw d T)) hK
    (fun z : Cube d × Rows d T => CubeSphere (d := d) (by omega) z.1)
    (fun z : Cube d × Rows d T => records (CubeSphere (d := d) (by omega) z.1) z.2)
    (fun i => show Measure.QuasiMeasurePreserving _ _ _ from cube_sample_observation_quasi hd i)
    (chordTest ε)
  rw [← lintegral_congr_ae he]
  exact (K.version hK).borel_cube_bound (K.version_borel hK) hd hε

lemma source_cube_chord_bound {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hd : 16 ≤ d)
    (hL : Admissible L ρ (CubePrior (by omega))) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (CubePrior (by omega)) ε ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have hp := (cubeSphere_preserving (by omega : 2 ≤ d)).prod
    (MeasurePreserving.id (ρ.prod (RowLaw d T)))
  have hf := hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε)
  have he : (∫⁻ z : Cube d × (Ω × Rows d T),
      experiment L (chordTest ε) (CubeSphere (d := d) (by omega) z.1,z.2)
      ∂(CubeLaw d).prod (ρ.prod (RowLaw d T))) = ChordSuccess L ρ (CubePrior (by omega)) ε := by
    calc
      _ = ∫⁻ z, experiment L (chordTest ε) z ∂((CubeLaw d).prod (ρ.prod (RowLaw d T))).map
          (Prod.map (CubeSphere (d := d) (by omega)) id) :=
        (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
      _ = _ := by rw [hp.map_eq]; rfl
  rw [← he]
  apply seed_average_bound (CubeLaw d) (RowLaw d T) ρ
    (hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving)
  filter_upwards [hL.completed] with ω hω
  exact (L ω).completed_cube_bound hω hd hε
end Policy
end MemoryPrecision.Kernel


end

end OAI
