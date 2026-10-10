import OAI.Geometry.NodalSets.Waves.FiniteWaveDerivativeBounds
import OAI.Geometry.NodalSets.Waves.GaussianPairMoments

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_iterated_apply (V : ι → Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (a : ι × Fin 2 → ℝ)
    (k : ℕ) (x : Coord) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (gaussianWaveField V a) x v =
      pairLinearSum (fun i ↦ iteratedFDeriv ℝ k (V i) x v) a := by
  classical
  let W : Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i))
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  change iteratedFDeriv ℝ k (Complex.reCLM ∘ W) x v = _
  rw [Complex.reCLM.iteratedFDeriv_comp_left hW.contDiffAt hk]
  change (iteratedFDeriv ℝ k W x v).re = _
  dsimp only [W]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((contDiff_const.mul (hV i)).of_le hk).contDiffAt)]
  simp only [sum_apply,Complex.re_sum,pairLinearSum_eq_complex]
  apply Finset.sum_congr rfl
  intro i _
  change (iteratedFDeriv ℝ k (gaussianCoefficient a i • V i) x v).re = _
  rw [iteratedFDeriv_const_smul_apply ((hV i).of_le hk).contDiffAt]
  rfl

lemma seeded_gaussian_iterated_apply (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (a : ι × Fin 2 → ℝ) (k : ℕ) (x : Coord) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x v =
      iteratedFDeriv ℝ k seed x v +
        pairLinearSum (fun i ↦ iteratedFDeriv ℝ k (V i) x v) a := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  change iteratedFDeriv ℝ k (seed + gaussianWaveField V a) x v = _
  rw [iteratedFDeriv_add_apply (hs.of_le hk).contDiffAt
    ((gaussianWaveField_contDiff V a hV).of_le hk).contDiffAt]
  simp only [add_apply,gaussianWaveField_iterated_apply V hV]

lemma seeded_gaussian_derivative_memLp (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (k : ℕ) (x : Coord) (v : Fin k → Coord) :
    MemLp (fun a ↦ iteratedFDeriv ℝ k
      (fun z ↦ seed z+gaussianWaveField V a z) x v) 2 gaussianPairs := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  simp_rw [seeded_gaussian_iterated_apply V seed hV hs]
  exact (memLp_const (μ := gaussianPairs (ι := ι)) (p := 2)
    (iteratedFDeriv ℝ k seed x v)).add (pairLinearSum_memLp_two _)

lemma seeded_gaussian_derivative_moment (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (k : ℕ) (x : Coord) (v : Fin k → Coord) :
    ∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x v)^2
      ∂gaussianPairs = (iteratedFDeriv ℝ k seed x v)^2 +
        ∑ i, ‖iteratedFDeriv ℝ k (V i) x v‖^2 := by
  simp_rw [seeded_gaussian_iterated_apply V seed hV hs]
  exact pairLinearSum_mean_square _ _

end
end Yau.Geometry

end OAI
