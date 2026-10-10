import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPenalty

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def scalarSign (b : Bool) : ℝ → ℝ := fun x => if b then -x else x

@[simp] theorem scalarSign_involutive (b : Bool) (x : ℝ) :
    scalarSign b (scalarSign b x) = x := by cases b <;> simp [scalarSign]

@[simp] theorem scalarSign_square (b : Bool) (x : ℝ) :
    (scalarSign b x)^2 = x^2 := by cases b <;> simp [scalarSign]

@[simp] theorem scalarSign_false : scalarSign false = id := by
  funext x; simp [scalarSign]

@[simp] theorem scalarSign_true : scalarSign true = fun x : ℝ => -x := by
  funext x; simp [scalarSign]

theorem scalarSign_continuous (b : Bool) : Continuous (scalarSign b) := by
  cases b <;> simp only [scalarSign_false,scalarSign_true] <;> fun_prop

def scalarSignEquiv (b : Bool) : ℝ ≃ᵐ ℝ where
  toFun := scalarSign b
  invFun := scalarSign b
  left_inv := scalarSign_involutive b
  right_inv := scalarSign_involutive b
  measurable_toFun := (scalarSign_continuous b).measurable
  measurable_invFun := (scalarSign_continuous b).measurable

theorem scalarSign_gaussian (b : Bool) :
    MeasurePreserving (scalarSign b) (gaussianReal 0 1) (gaussianReal 0 1) := by
  refine ⟨(scalarSign_continuous b).measurable, ?_⟩
  cases b
  · simp only [scalarSign_false,Measure.map_id]
  · simpa only [scalarSign_true,neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))

theorem scalarSign_volume (b : Bool) :
    MeasurePreserving (scalarSign b) (volume : Measure ℝ) volume := by
  cases b
  · simpa only [scalarSign_false] using
      (MeasurePreserving.id (volume : Measure ℝ))
  · simpa only [scalarSign_true] using Measure.measurePreserving_neg (volume : Measure ℝ)

def coordinateSign : (n : ℕ) → (Fin n → Bool) → ParameterSpace n → ParameterSpace n
  | 0, _, z => z
  | n+1, b, z => (coordinateSign n (fun i => b i.castSucc) z.1,scalarSign (b (Fin.last n)) z.2)

theorem coordinateSign_involutive (n : ℕ) (b : Fin n → Bool) :
    Function.Involutive (coordinateSign n b) := by
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
    intro z
    change (coordinateSign n (fun i => b i.castSucc)
      (coordinateSign n (fun i => b i.castSucc) z.1),
      scalarSign (b (Fin.last n)) (scalarSign (b (Fin.last n)) z.2)) = z
    rw [ih _ z.1, scalarSign_involutive]

theorem coordinateSign_continuous (n : ℕ) (b : Fin n → Bool) :
    Continuous (coordinateSign n b) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((ih _).comp continuous_fst).prodMk ((scalarSign_continuous _).comp continuous_snd)

def coordinateSignEquiv (n : ℕ) (b : Fin n → Bool) : ParameterSpace n ≃ᵐ ParameterSpace n where
  toFun := coordinateSign n b
  invFun := coordinateSign n b
  left_inv := coordinateSign_involutive n b
  right_inv := coordinateSign_involutive n b
  measurable_toFun := (coordinateSign_continuous n b).measurable
  measurable_invFun := (coordinateSign_continuous n b).measurable

theorem coordinateSign_square (n : ℕ) (b : Fin n → Bool) (z : ParameterSpace n) :
    coordinateSquare n (coordinateSign n b z) = coordinateSquare n z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [coordinateSign,coordinateSquare,ih,scalarSign_square]

theorem coordinateSign_fiber (n : ℕ) (b : Fin n → Bool) (t : ℝ) :
    MeasurePreserving (coordinateSign n b) (fiberMeasure n t) (fiberMeasure n t) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    exact (ih (fun i => b i.castSucc)).prod (scalarSign_volume (b (Fin.last n)))

theorem gaussianStep_sign {n : ℕ} {f : ParameterSpace (n+1) → ℝ} (b : Fin (n+1) → Bool)
    (hf : ∀ z, f (coordinateSign (n+1) b z) = f z) (m : ℝ) (z : ParameterSpace n) :
    gaussianStep m f (coordinateSign n (fun i => b i.castSucc) z) = gaussianStep m f z := by
  have he (y : ℝ) : f (coordinateSign n (fun i => b i.castSucc) z,y) =
      f (z,scalarSign (b (Fin.last n)) y) := by
    simpa only [coordinateSign,scalarSign_involutive] using
      hf (z,scalarSign (b (Fin.last n)) y)
  have hi (g : ℝ → ℝ) : (∫ y, g (scalarSign (b (Fin.last n)) y) ∂gaussianReal 0 1) =
      ∫ y, g y ∂gaussianReal 0 1 :=
    (scalarSign_gaussian _).integral_comp (scalarSignEquiv _).measurableEmbedding g
  unfold gaussianStep positiveGaussianLogStep
  simp only [he]
  rw [hi (fun y => f (z,y)), hi (fun y => Real.exp (m*f (z,y)))]

theorem hierarchyPenalty_sign (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (b : Fin n → Bool)
    (hf : ∀ z, f (coordinateSign n b z) = f z) (z : ParameterSpace n) :
    hierarchyPenalty n m u f (coordinateSign n b z) = hierarchyPenalty n m u f z := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change (u-m (Fin.last n))*f (coordinateSign (n+1) b z) +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) (coordinateSign n (fun i => b i.castSucc) z.1) = _
    rw [hf, ih _ _ _ _ (gaussianStep_sign b hf (m (Fin.last n)))]
    rfl

theorem affineLogPartition_sign {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (b : Fin n → Bool) (p : Equiv.Perm S)
    (hc : ∀ s, c (p s) = c s) (hU : ∀ s z, U s (coordinateSign n b z) = U (p s) z)
    (z : ParameterSpace n) :
    affineLogPartition c U (coordinateSign n b z) = affineLogPartition c U z := by
  unfold affineLogPartition
  congr 1
  have he : (fun s => Real.exp (c s+U s (coordinateSign n b z))) =
      fun s => Real.exp (c (p s)+U (p s) z) := by
    funext s; rw [hc,hU]
  rw [he]
  exact Equiv.sum_comp p (fun s : S => Real.exp (c s+U s z))

theorem fixed_spin_gauge_integral (n : ℕ) (m : Fin n → ℝ)
    {S : Type} [Fintype S] [Nonempty S]
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (b : Fin n → Bool) (p : Equiv.Perm S)
    (hc : ∀ s, c (p s) = c s) (hU : ∀ s z, U s (coordinateSign n b z) = U (p s) z)
    (s : S) (g g' : ParameterSpace n → ℝ)
    (hg : ∀ z, g (coordinateSign n b z) = g' z) :
    (∫ z, g z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z + U s z -
        hierarchyPenalty n m 1 (affineLogPartition c U) z) ∂fiberMeasure n 0) =
    (∫ z, g' z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z + U (p s) z -
        hierarchyPenalty n m 1 (affineLogPartition c U) z) ∂fiberMeasure n 0) := by
  have hfs := affineLogPartition_sign n c U b p hc hU
  have hp := hierarchyPenalty_sign n m 1 (affineLogPartition c U) b hfs
  have hi := (coordinateSign_fiber n b 0).integral_comp
    (coordinateSignEquiv n b).measurableEmbedding
    (fun z => g z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
      hierarchyPenalty n m 1 (affineLogPartition c U) z))
  rw [← hi]
  congr 1
  funext z
  rw [hg,coordinateSign_square,hU,hp]

end SK.Analytic

end
end
end
end
end
end

end OAI
