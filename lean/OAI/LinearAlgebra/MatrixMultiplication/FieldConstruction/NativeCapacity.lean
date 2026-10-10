import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.HalfLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Entropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.LeafRates
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Priority
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Sums
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.StageC
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CapacityAlgebra

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

def marginal (support : List Shape) (p : Shape → ℝ) (side : Fin 3)
    (k : Fin 17) : ℝ :=
  (support.map fun u => if u side = k.val then p u else 0).sum

def pairLaw (support : List Shape) (s : Shape) (p : Shape → ℝ)
    (q : Shape → A → ℝ) (ij : A × A) : ℝ :=
  (support.map fun u => p u * q u ij.1 * q (complement s u) ij.2).sum

def designated (priority : Placement) (position : Fin 3) (u : Shape) : Prop :=
  if position = 1 then u (priority 2) = 0
  else u (priority 0) = 0 ∨ u (priority 1) = 0

def singletonEntropy (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ) : ℝ :=
  (support.map fun u => if designated priority position u then
    p u * homogeneousEntropy (q u) else 0).sum

def residualLaw (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (k : Fin 17) (a : A) : ℝ :=
  (support.map fun u =>
    if ¬ designated priority position u ∧ u (priority position) = k.val
    then p u * q u a else 0).sum

def groupedEntropy (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ) : ℝ :=
  singletonEntropy support p priority position q +
    ∑ k : Fin 17, homogeneousEntropy (residualLaw support p priority position q k)

def nativeCapacity (support : List Shape) (s : Shape) (p : Shape → ℝ)
    (priority : Placement) (q : Shape → Fin 3 → A → ℝ) : Staggering.Capacity :=
  fun i => if i = 0 then homogeneousEntropy (marginal support p (priority 0))
    else homogeneousEntropy (pairLaw support s p (fun u => q u (priority i))) -
      2 * groupedEntropy support p priority i (fun u => q u (priority i))

@[simp] theorem nativeCapacity_first (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (q : Shape → Fin 3 → A → ℝ) :
    nativeCapacity support s p priority q 0 =
      homogeneousEntropy (marginal support p (priority 0)) := by
  simp [nativeCapacity]

theorem nativeCapacity_sharing (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (q : Shape → Fin 3 → A → ℝ)
    (i : Fin 3) (hi : i ≠ 0) :
    nativeCapacity support s p priority q i =
      homogeneousEntropy (pairLaw support s p (fun u => q u (priority i))) -
        2 * groupedEntropy support p priority i (fun u => q u (priority i)) := by
  simp only [nativeCapacity, ite_eq_right hi]

theorem residual_entropy_eq_mass_mul (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ) (k : Fin 17)
    (hm : ∑ a, residualLaw support p priority position q k a ≠ 0) :
    homogeneousEntropy (residualLaw support p priority position q k) =
      (∑ a, residualLaw support p priority position q k a) *
        finiteEntropy (fun a => residualLaw support p priority position q k a /
          ∑ b, residualLaw support p priority position q k b) :=
  homogeneousEntropy_eq_mass_mul _ hm

def stageACapacity (g : Shape) : Staggering.Capacity :=
  nativeCapacity (below g) g (fun u => (stageALaw g u : ℝ))
    (Equiv.refl (Fin 3)) (fun u w a => (halfLaw u w a : ℝ))

def stageBCapacity (t : Shape) : Staggering.Capacity :=
  nativeCapacity (below t) t (fun u => (stageBLaw t u : ℝ))
    (stageBPriority t) (fun u w a => (littleLaw t u w a : ℝ))

def stageCCapacity (t u : Shape) (part : Fin 3) : Staggering.Capacity :=
  fun i => if i = part then binaryEntropyRate (binaryParameter t u) else Real.log 2

def nativeLA : Staggering.Capacity := fun i =>
  (positiveInitial.map fun g => (initialLaw g : ℝ) * stageACapacity g i).sum

def nativeLB : Staggering.Capacity := fun i =>
  (positiveSecond.map fun t => (secondMass t : ℝ) * stageBCapacity t i).sum

def interiorPairs : List (Shape × Shape) :=
  positiveSecond.flatMap fun t =>
    ((below t).filter positive).map fun u => (t, u)

def interiorMass (tu : Shape × Shape) : ℝ := littleMass tu.1 tu.2

def interiorEntropy (tu : Shape × Shape) : ℝ :=
  binaryEntropyRate (binaryParameter tu.1 tu.2)

def nativeT : ℝ := (interiorPairs.map interiorMass).sum

def nativeB : ℝ :=
  (interiorPairs.map fun tu => interiorMass tu *
    (2 * Real.log 2 + interiorEntropy tu)).sum / 3

def nativeHigh : ℝ := nativeT * Real.log 2

def nativeCstar : ℝ := Staggering.totalCapacity nativeLA nativeLB nativeB

def nativeLambda : Fin 3 → ℝ :=
  Staggering.balanceFraction nativeLA nativeLB nativeHigh nativeB

def nativeLC (allocation : Fin 3 → ℝ) : Staggering.Capacity := fun i =>
  (interiorPairs.map fun tu => interiorMass tu *
    ((1 - allocation i) * Real.log 2 + allocation i * interiorEntropy tu)).sum

theorem nativeLC_expansion (allocation : Fin 3 → ℝ) (i : Fin 3) :
    nativeLC allocation i = nativeHigh - 3 * allocation i * (nativeHigh - nativeB) := by
  unfold nativeLC nativeHigh nativeT nativeB
  have h : ∀ xs : List (Shape × Shape),
      (xs.map fun tu => interiorMass tu *
        ((1 - allocation i) * Real.log 2 + allocation i * interiorEntropy tu)).sum =
      (xs.map interiorMass).sum * Real.log 2 - 3 * allocation i *
        ((xs.map interiorMass).sum * Real.log 2 -
          (xs.map fun tu => interiorMass tu *
            (2 * Real.log 2 + interiorEntropy tu)).sum / 3) := by
    intro xs
    induction xs with
    | nil => simp
    | cons tu xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  exact h interiorPairs

theorem nativeLC_balanced (hgap : nativeB < nativeHigh) (i : Fin 3) :
    nativeLC nativeLambda i = nativeCstar - (nativeLA i + nativeLB i) := by
  rw [nativeLC_expansion]
  exact Staggering.thirdCapacity_eq nativeLA nativeLB nativeHigh nativeB hgap i

theorem native_balanced (hgap : nativeB < nativeHigh) (i : Fin 3) :
    nativeLA i + nativeLB i + nativeLC nativeLambda i = nativeCstar := by
  rw [nativeLC_balanced hgap]
  ring

def nativeBeta : ℝ :=
  Staggering.boundaryDeficit nativeLA nativeLB (nativeLC nativeLambda) nativeCstar

theorem nativeBeta_nonnegative (hgap : nativeB < nativeHigh) : 0 ≤ nativeBeta :=
  Staggering.boundaryDeficit_nonneg _ _ _ _ (native_balanced hgap)

end MatrixMultiplication.AllFieldNativeCapacity

end

end OAI
