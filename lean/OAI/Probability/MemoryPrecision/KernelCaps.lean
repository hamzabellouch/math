import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeExperiment
import OAI.Probability.MemoryPrecision.KernelEvaluation
import OAI.Probability.MemoryPrecision.SphereCaps

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression
instance {d : ℕ} [NeZero d] : IsProbabilityMeasure (UniformSphere d) :=
  (show IsProbabilityMeasure (NoiselessRegression.sphereLaw (E := Vector d)) from inferInstance)
instance (d T : ℕ) : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance

namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma chordTest_eq_cap (ε : ℝ) (s v : MemoryPrecision.Kernel.Sphere d) :
    chordTest ε (s,v) = capWeight v.val ε s.val := by
  classical
  change (if dist v.val s.val ≤ ε then 1 else 0) =
    (if dist s.val v.val ≤ ε then 1 else 0)
  rw [dist_comm]

lemma output_chord_sphere_local (hd : 1 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    SphereBallBound (K.outputTest (chordTest ε) t j)
      ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)) α := by
  have : NeZero d := ⟨by omega⟩
  intro z r hr
  change (∫⁻ s in {s : MemoryPrecision.Kernel.Sphere d | dist s.val z ≤ r},
    ∫⁻ v, chordTest ε (s,v) ∂K.output t j ∂UniformSphere d) ≤ _
  have hm : Measurable (Function.uncurry (fun s v : MemoryPrecision.Kernel.Sphere d => chordTest ε (s,v))) :=
    measurable_chordTest ε
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hb (v : MemoryPrecision.Kernel.Sphere d) := sphere_cap_real_mass hd v.val hε hα hαn z r hr
  simp_rw [chordTest_eq_cap]
  exact (lintegral_mono hb).trans_eq (by simp)

lemma output_chord_cube_local (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    CubeLocal (fun u => K.outputTest (chordTest ε) t j (CubeSphere hd u))
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ)) := by
  intro z r hr
  change (∫⁻ u in CubeBall d z r, ∫⁻ v, chordTest ε (CubeSphere hd u,v)
    ∂K.output t j ∂CubeLaw d) ≤ _
  have hf : Measurable (Function.uncurry (fun (u : Cube d) (v : MemoryPrecision.Kernel.Sphere d) =>
      chordTest ε (CubeSphere hd u,v))) :=
    (measurable_chordTest ε).comp ((cubeSphere_measurable hd).comp measurable_fst |>.prodMk measurable_snd)
  rw [lintegral_lintegral_swap hf.aemeasurable]
  simp_rw [chordTest_eq_cap]
  change (∫⁻ v : MemoryPrecision.Kernel.Sphere d, ∫⁻ u in CubeBall d z r,
      capWeight v.val ε (CubeEmbedding d u) ∂CubeLaw d ∂K.output t j) ≤ _
  have hb (v : MemoryPrecision.Kernel.Sphere d) := cube_cap_local hd v.val hε z r hr
  exact (lintegral_mono hb).trans_eq (by simp)

lemma output_chord_sphere_total (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    (∫⁻ s, K.outputTest (chordTest ε) t j s ∂UniformSphere d) ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have h := sphere_mass_bound (K.output_chord_sphere_local hd hε (α := 0) le_rfl (by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith) t j)
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  simpa only [UniformSphere, SpherePrior,sub_zero, ← hn, Real.rpow_natCast] using h

lemma angleTest_le_chordTest (ε : ℝ) (x : MemoryPrecision.Kernel.Sphere d × MemoryPrecision.Kernel.Sphere d) :
    angleTest ε x ≤ chordTest ε x := by
  classical
  by_cases ha : Real.arccos ⟪x.2.val,x.1.val⟫ ≤ ε
  · have hc : dist x.2.val x.1.val ≤ ε := (chord_le_arccos x.2 x.1).trans ha
    simp [angleTest, chordTest, ha, hc]
  · simp [angleTest, ha]

lemma eval_mono {X : Type*} {w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞}
    (h : ∀ n j s, w n j s ≤ v n j s) (n k : ℕ) (j : MemoryPrecision.Kernel.State M)
    (s : X) (obs : Observations d k) : K.eval w n k j s obs ≤ K.eval v n k j s obs := by
  induction k generalizing n j with
  | zero => exact h n j s
  | succ k ih =>
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul' le_rfl
    split
    · exact h _ _ _
    · exact ih _ _ _

lemma pathValue_mono {X : Type*} {w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞}
    (h : ∀ n j s, w n j s ≤ v n j s) (s : X) (obs : Observations d T) :
    K.pathValue w s obs ≤ K.pathValue v s obs := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul' le_rfl
  split
  · exact h _ _ _
  · exact K.eval_mono h _ _ _ _ _

lemma success_le_chord {Ω : Type*} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) (π : Measure (MemoryPrecision.Kernel.Sphere d)) (ε : ℝ) :
    Success L ρ π ε ≤ ChordSuccess L ρ π ε := by
  apply lintegral_mono
  intro z
  exact (L z.2.1).pathValue_mono (fun n j s => lintegral_mono (fun v => angleTest_le_chordTest ε (s,v))) _ _
end Policy
end MemoryPrecision.Kernel


end

end OAI
