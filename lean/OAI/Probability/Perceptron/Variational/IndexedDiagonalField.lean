import Mathlib
import OAI.Probability.Perceptron.Pressure.VectorPartition
import OAI.Probability.Perceptron.Variational.FiniteGaussianRow
import OAI.Probability.Perceptron.Variational.TensorFeatures

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

def hierarchyRowCoefficients (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ) : Fin (n+1) → I → ℝ :=
  Fin.cases root (fun d => step (n-1-d.val))

omit [MeasurableSpace S] in
lemma indexedGaussianRow_diagonal_identity (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
      (indexedGaussianRowLength (I := I) n) g x =
    inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
      ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
        (indexedGaussianDisorder n I g).2) x.2 0) := by
  rw [indexedGaussianRow_field]
  change _ = inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
    ((fun _ => diagonalMark root (countableGaussianVectors g (Sum.inl ()))),
      indexedMarksFromVertices n (fun v => countableGaussianVectors g (Sum.inr v))) x.2 0)
  rw [indexedLeafState_gaussianLinear,inner_add_right,inner_sum,Fin.sum_univ_succ]
  simp only [Nat.zero_add,hierarchyRowCoefficients,Fin.cases_zero,Fin.cases_succ,
    indexedLeafSharedVertex]
  congr 1
  · simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (root i * g (countableCoordinate (Sum.inl (),i))) * V x.1 i
    ring
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (step (n-1-d.val) i * g (countableCoordinate (Sum.inr (indexedLeafVertex n x.2 d),i))) * V x.1 i
    ring

end

section Partition
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_lipschitz {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K : ℝ} {C : ℝ≥0}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    LipschitzWith C (vectorLogPartition ρ W V) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,vectorLogPartition,vectorPartition]
  apply abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm hVm hW hV y)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm hVm hW hV y)
  intro s
  simp only [add_sub_add_left_eq_sub,← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg _))
end Partition

def normalizedPatternEnergy (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (x : NormalizedSpin N) : ℝ :=
  ∑ a, f (∑ i, g a i*x.val i)

lemma normalizedPatternEnergy_continuous (N M : ℕ) (f : ℝ →ᵇ ℝ) :
    Continuous (fun p : (Fin M → Fin N → ℝ) × NormalizedSpin N =>
      normalizedPatternEnergy N M f p.1 p.2) := by
  unfold normalizedPatternEnergy
  fun_prop

lemma normalizedPatternEnergy_bound (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N M f g x| ≤ (M:ℝ)*‖f‖ := by
  unfold normalizedPatternEnergy
  calc
    _ ≤ ∑ a : Fin M, |f (∑ i, g a i*x.val i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin M, ‖f‖ := Finset.sum_le_sum (fun _ _ => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _)
    _ = _ := by simp

def enrichedTerminal (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) (a : EnrichedMark (n+1) (n+1) p) : ℝ :=
  vectorLogPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f g)
    (fun x => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) a - (n+1:ℕ)*htop

def enrichedFeatureBound (N : ℕ) (u : Fin N → ℝ) : ℝ≥0 :=
  ⟨Real.sqrt ((N:ℝ)+∑ j, perturbationAmplitude N u j^2),Real.sqrt_nonneg _⟩

lemma sourceEnrichedFeature_norm (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (x : NormalizedSpin N) : ‖sourceEnrichedFeature N p u x‖=enrichedFeatureBound N u := by
  rw [sourceEnrichedFeature,enrichedFeature_norm,Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

lemma enrichedTerminal_lipschitz (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) : LipschitzWith (enrichedFeatureBound (n+1) u)
      (enrichedTerminal n M f g p u htop) := by
  have hW : Continuous (normalizedPatternEnergy (n+1) M f g) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp
    (continuous_const.prodMk continuous_id)
  have hV : Continuous (fun x : NormalizedSpin (n+1) =>
      innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) :=
    (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hL := vectorLogPartition_lipschitz (unitSphereLaw (n+1)) hW.measurable hV.measurable
    (normalizedPatternEnergy_bound (n+1) M f g)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm])
  intro x y
  simpa only [enrichedTerminal,edist_sub_right] using hL x y

def enrichedCoordinateLevel {N k : ℕ} (p d : Fin N → ℕ)
    (h : Fin (k+1) → ℝ) (l : Fin (k+1)) (i : EnrichedIndex N N p) : ℝ :=
  match i with
  | .inl _ => 2*h l
  | .inr ⟨j,_⟩ => ((l.val:ℝ)/(k+1:ℕ))^(d j)

def enrichedRootMap {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) :
    EnrichedMark N N p →L[ℝ] EnrichedMark N N p :=
  diagonalMark (fun i => Real.sqrt (enrichedCoordinateLevel p d h 0 i))

def enrichedIncrementMap {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (j : ℕ) : EnrichedMark N N p →L[ℝ] EnrichedMark N N p :=
  if hj : j<k then diagonalMark (fun i => Real.sqrt
    (enrichedCoordinateLevel p d h ⟨k-j,by omega⟩ i-
     enrichedCoordinateLevel p d h ⟨k-j-1,by omega⟩ i)) else 0

def enrichedCascadeLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ)
    (a : EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) : ℝ :=
  let step := gaussianLinearMarkStep (enrichedIncrementMap p d h)
  let H := fun x => enrichedTerminal n M f g p u (h (Fin.last k)) (x 0)
  let x := fun _ => enrichedRootMap p d h a.1
  Real.log (decoratedTerminalTotal step H k (x,a.2)/
    decoratedTerminalTotal step (fun _ => 0) k (x,a.2))

end SphericalPerceptronFreeEnergy

end

end OAI
