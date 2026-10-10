import OAI.Geometry.EinsteinFour.ScalarPoissonKernelDerivative
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelUniqueness

namespace OAI

/-! Passing the first and second weak derivatives through strong L2 limits.
This closes the nonlinear H2 calculation after its explicit product limits. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalar_L2_weak_derivative_limit (f g : ℕ → L2) (u v : L2)
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) (i : Fin 4)
    (heq : ∀ n, scalarCoordinateDerivative i (f n : T) = (g n : T)) :
    scalarCoordinateDerivative i (u : T) = (v : T) := by
  have hU := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hf
  have hV := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hg
  have hD := (lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ i)).continuous.continuousAt.tendsto.comp hU
  apply tendsto_nhds_unique hD
  convert hV using 1
  · funext n
    exact heq n
  · rfl

/-- Strong convergence of the two jets supplies H2 for their value limit. -/
theorem scalar_H2_of_strong_jets (f : ℕ → L2) (G : Fin 4 → ℕ → L2)
    (H : Fin 4 → Fin 4 → ℕ → L2) (u : L2) (g : Fin 4 → L2) (h : Fin 4 → Fin 4 → L2)
    (hf : Tendsto f atTop (𝓝 u))
    (hg : ∀ i, Tendsto (G i) atTop (𝓝 (g i)))
    (hh : ∀ i j, Tendsto (H i j) atTop (𝓝 (h i j)))
    (hD : ∀ n i, scalarCoordinateDerivative i (f n : T) = (G i n : T))
    (hDD : ∀ n i j, scalarCoordinateDerivative i (G j n : T) = (H i j n : T)) :
    MemSobolev 2 2 (u : T) := by
  have hDu (i : Fin 4) : scalarCoordinateDerivative i (u : T) = (g i : T) :=
    scalar_L2_weak_derivative_limit f (G i) u (g i) hf (hg i) i (fun n => hD n i)
  have hDg (i j : Fin 4) : scalarCoordinateDerivative i (g j : T) = (h i j : T) :=
    scalar_L2_weak_derivative_limit (G j) (H i j) (g j) (h i j) (hg j) (hh i j) i
      (fun n => hDD n i j)
  have hgH1 (j : Fin 4) : MemSobolev 1 2 (g j : T) := by
    have hs := scalar_memSobolev_succ_iff 0 (g j : T)
    norm_num at hs
    rw [hs]
    refine ⟨memSobolev_zero_iff.mpr ⟨g j, rfl⟩, fun i => ?_⟩
    rw [hDg i j]
    exact memSobolev_zero_iff.mpr ⟨h i j, rfl⟩
  have huH1 : MemSobolev 1 2 (u : T) := by
    have hs := scalar_memSobolev_succ_iff 0 (u : T)
    norm_num at hs
    rw [hs]
    refine ⟨memSobolev_zero_iff.mpr ⟨u, rfl⟩, fun i => ?_⟩
    rw [hDu i]
    exact memSobolev_zero_iff.mpr ⟨g i, rfl⟩
  have hc := (scalar_memSobolev_succ_iff 1 (u : T)).mpr
    ⟨huH1, fun i => by rw [hDu i]; exact hgH1 i⟩
  norm_num at hc
  exact hc

end
end PositiveEinsteinFour.Geometry

end OAI
