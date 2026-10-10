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
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma borel_sphere_bound (hK : K.Borel) (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  rw [lintegral_prod _ (K.experiment_fixed_measurable hK (measurable_chordTest ε)).aemeasurable]
  apply K.integral_pathValue_bound (K.outputTest (chordTest ε)) Subtype.val hK
    (K.outputTest_measurable (measurable_chordTest ε)) measurable_subtype_coe (UniformSphere d)
  intro r hr j
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hb := stoch_sphere_mass hd (show 1 ≤ 2^M from one_le_pow₀ (by norm_num))
    (K.marginal_measurable hK) (fun n j obs => (K.marginal_sum n j obs).le)
    (K.outputTest_measurable (measurable_chordTest ε))
    (K.outputTest_le_one (chordTest_le_one ε))
    (H := (3*4^d)*ε^((d:ℝ)-1-α)) (by positivity) hαlo hαhi
    (K.output_chord_sphere_local (by omega) hε (by linarith) (by linarith))
    (BlockCount T (d/8)) r (hr.trans (blockCount_mul_ge T (by omega))) 0 j
  exact sphere_mass_bound hb

lemma completed_sphere_bound (hK : K.Completed) (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  have he := K.version_pathValue_ae ((UniformSphere d).prod (RowLaw d T)) hK Prod.fst
    (fun z : MemoryPrecision.Kernel.Sphere d × Rows d T => records z.1 z.2)
    (fun i => show Measure.QuasiMeasurePreserving _ _ _ from
      sphere_sample_observation_quasi (by simpa using (show 3 ≤ d by omega)) i) (chordTest ε)
  rw [← lintegral_congr_ae he]
  exact (K.version hK).borel_sphere_bound (K.version_borel hK) hd hε hαlo hαhi

lemma chord_real_bound {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hL : Admissible L ρ (UniformSphere d))
    (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    ChordSuccess L ρ (UniformSphere d) ε ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  apply seed_average_bound (UniformSphere d) (RowLaw d T) ρ
    (hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε))
  filter_upwards [hL.completed] with ω hω
  exact (L ω).completed_sphere_bound hω hd hε hαlo hαhi

lemma zero_fixed_sphere_bound {d M : ℕ} (K : Policy d M 0) (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d 0,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d 0)) ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have : NeZero d := ⟨by omega⟩
  have he (s : MemoryPrecision.Kernel.Sphere d) (obs : Observations d 0) :
      K.pathValue (K.outputTest (chordTest ε)) s obs =
        ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 s := by
    unfold pathValue
    simp only [eval, ite_self]
  simp_rw [he]
  have hm : Measurable (fun s : MemoryPrecision.Kernel.Sphere d =>
      ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 s) :=
    Finset.measurable_sum _ (fun a _ => (K.outputTest_measurable (measurable_chordTest ε) 0 a.2).const_mul _)
  have hm' : Measurable (fun z : MemoryPrecision.Kernel.Sphere d × Rows d 0 =>
      ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 z.1) :=
    hm.comp measurable_fst
  rw [lintegral_prod _ hm'.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_finsetSum _ (fun a _ =>
    (K.outputTest_measurable (measurable_chordTest ε) 0 a.2).const_mul _)]
  calc
    _ = ∑ a : Action M, K.initial a *
        (∫⁻ s, K.outputTest (chordTest ε) 0 a.2 s ∂UniformSphere d) := by
      apply Finset.sum_congr rfl
      intro a _
      exact lintegral_const_mul _ (K.outputTest_measurable (measurable_chordTest ε) 0 a.2)
    _ ≤ ∑ a : Action M, K.initial a * ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (K.output_chord_sphere_total hd hε 0 a.2))
    _ = _ := by rw [← Finset.sum_mul, K.initial_sum, one_mul]

lemma chord_zero_bound {d M : ℕ} {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M 0)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hL : Admissible L ρ (UniformSphere d))
    (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have : NeZero d := ⟨by omega⟩
  apply seed_average_bound (UniformSphere d) (RowLaw d 0) ρ
    (hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε))
  exact Filter.Eventually.of_forall (fun ω => (L ω).zero_fixed_sphere_bound hd hε)
end Policy
end MemoryPrecision.Kernel


end

end OAI
