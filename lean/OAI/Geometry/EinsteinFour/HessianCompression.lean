import OAI.Geometry.EinsteinFour.GradientPairing
import OAI.Geometry.EinsteinFour.GradientCoordinates
import OAI.Geometry.EinsteinFour.RealVectorCost
import OAI.Geometry.EinsteinFour.CoupledCasimir
import OAI.Geometry.EinsteinFour.HighestMinusForm

namespace OAI

/-! Curvature compression on all actual inner-Bianchi Hessian tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def rawQuaternion (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  quaternion s (Z a b)

def rawMatrixAt (Z : RawGradient) (j : Fin 4) : Mat := fun a b => Z a b j

theorem hessianPairing_slices (X Y : Hessian) :
    hessianPairing X Y = ∑ i, rawPairing (rawSlice X i) (rawSlice Y i) := by
  rw [← tensorCoordinates_pairing]
  simp only [Fintype.sum_prod_type, tensorCoordinates, rawPairing, rawCoordinates, rawSlice]

theorem hessianNormSq_slices (X : Hessian) :
    hessianNormSq X = ∑ i, rawNorm (rawSlice X i) := by
  rw [← hessianPairing_self, hessianPairing_slices]
  apply Finset.sum_congr rfl
  intro i _
  rw [rawPairing_vectors]
  simp only [rawNorm, real_inner_self_eq_norm_sq]

theorem rawSlice_eq_innerSlice (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j)) (i : Fin 4) :
    rawSlice X i = (innerSlice X i).matrix := by
  funext a b
  exact (innerSlice_matrix X i (hmatrix i) a b).symm

theorem outerAction_rawSlice (s : Fin 3) (X : Hessian) (i : Fin 4) :
    rawSlice (outerAction s X) i =
      ∑ k : Fin 4, quaternionMatrix s i k • rawSlice X k := by
  funext a b
  ext j
  have h := quaternionMatrix_apply s (WithLp.toLp 2 (fun k => X k j a b)) i
  simpa [rawSlice, outerAction, Fin.sum_univ_four] using h.symm

theorem hessianPairing_outer_inner (s : Fin 3) (X : Hessian) :
    hessianPairing (outerAction s X) (innerAction s X) =
      ∑ i, ∑ k, quaternionMatrix s i k *
        rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i)) := by
  rw [hessianPairing_slices]
  simp_rw [outerAction_rawSlice, rawPairing_sum_left, rawPairing_smul_left,
    innerAction_rawSlice]

private theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem rawQuaternion_pairing (s : Fin 3) (Z W : RawGradient) :
    rawPairing (rawQuaternion s Z) W =
      ∑ j, ∑ k, quaternionMatrix s j k *
        matrixPairing (rawMatrixAt Z k) (rawMatrixAt W j) := by
  simp only [rawPairing, rawCoordinates, rawQuaternion, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← quaternionMatrix_apply]
  simp only [Finset.sum_mul]
  rw [sum_rotate]
  simp only [rawMatrixAt, matrixPairing, Finset.mul_sum, mul_assoc]

/-- The derivative-slot quadratic form retains arbitrary inner-Bianchi slices. -/
theorem derivativeSlotForm_slices (s : Fin 3) (X : Hessian) :
    derivativeSlotForm s X = ∑ i, ∑ k, quaternionMatrix s i k *
      rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) := by
  have hm (k l : Fin 4) : rawMatrixAt (rawSlice X k) l = X k l := rfl
  simp_rw [rawQuaternion_pairing, hm]
  simp only [Finset.mul_sum, mul_assoc, derivativeSlotForm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- The skew outer quaternion converts the compressed inner action into the
cross term in the total-plus energy. No symmetry of the outer slots is used. -/
theorem derivativeSlotForm_inner_cross (s : Fin 3) (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    derivativeSlotForm s X =
      -(1 / 5 : ℝ) * hessianPairing (outerAction s X) (innerAction s X) := by
  have hr := rawSlice_eq_innerSlice X (fun i j => (hmatrix i j).1)
  have hb (i : Fin 4) : (innerSlice X i).bianchi :=
    innerSlice_bianchi X i (fun j => (hmatrix i j).1) (hbianchi i)
  have hc (i k : Fin 4) :
      rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) =
        (1 / 5 : ℝ) * rawPairing (rawGradientGenerator s (rawSlice X k))
          (rawSlice X i) := by
    simp_rw [hr]
    change rawPairing (derivativeQuaternion s (innerSlice X k)).matrix
      (innerSlice X i).matrix = _
    exact derivativeQuaternion_pairing s (innerSlice X k) (innerSlice X i) (hb k) (hb i)
  rw [derivativeSlotForm_slices, hessianPairing_outer_inner]
  simp_rw [hc]
  have hswap : (∑ i, ∑ k, quaternionMatrix s i k *
      rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) =
        -(∑ i, ∑ k, quaternionMatrix s i k *
          rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [quaternionMatrix_skew s k i, rawPairing_comm]
    ring
  calc
    _ = (1 / 5 : ℝ) * (∑ i, ∑ k, quaternionMatrix s i k *
        rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hswap]; ring

theorem outerAction_norm (s : Fin 3) (X : Hessian) :
    hessianNormSq (outerAction s X) = hessianNormSq X := by
  have h (a b : Fin 3) (j : Fin 4) :
      (∑ i : Fin 4, outerAction s X i j a b ^ 2) = ∑ i, X i j a b ^ 2 := by
    have hn := quaternion_norm_sq s (WithLp.toLp 2 (fun i => X i j a b))
    simpa only [outerAction, EuclideanSpace.real_norm_sq_eq] using hn
  unfold hessianNormSq
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => X i j a b ^ 2)]
  simp_rw [h]

theorem matrixSlotForm_slices (s : Fin 3) (X : Hessian) :
    matrixSlotForm s X = ∑ i, ∑ b, ‖rawSlice X i s b‖ ^ 2 := by
  simp only [matrixSlotForm, rawSlice, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- The matrix-row energy identity applies independently to every outer slice. -/
theorem innerAction_norm (s : Fin 3) (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    hessianNormSq (innerAction s X) + 40 * matrixSlotForm s X =
      25 * hessianNormSq X := by
  have hr := rawSlice_eq_innerSlice X (fun i j => (hmatrix i j).1)
  have h (i : Fin 4) : rawNorm (rawGradientGenerator s (rawSlice X i)) +
      40 * (∑ b, ‖rawSlice X i s b‖ ^ 2) = 25 * rawNorm (rawSlice X i) := by
    have hh := generator_row_energy s (innerSlice X i)
      (innerSlice_traceFree X i (fun j => (hmatrix i j).2))
      (innerSlice_bianchi X i (fun j => (hmatrix i j).1) (hbianchi i))
    simpa only [rawNorm, Tensor.squaredNorm, ← hr i] using hh
  have hs := congrArg (fun f : Fin 4 → ℝ => ∑ i, f i) (funext h)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simpa only [hessianNormSq_slices, innerAction_rawSlice, matrixSlotForm_slices] using hs

private theorem hessianNormSq_add (X Y : Hessian) :
    hessianNormSq (X + Y) = hessianNormSq X + hessianNormSq Y +
      2 * hessianPairing X Y := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) ^ 2) = _
  have hp (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  simp only [hp, hessianNormSq, hessianPairing, Finset.sum_add_distrib,
    ← Finset.mul_sum]

/-- The exact directional curvature identity on the whole actual
inner-Bianchi tensor space, before restriction to the highest component. -/
theorem curvature_directional_identity (s : Fin 3) (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    10 * derivativeSlotForm s X + 40 * matrixSlotForm s X +
      hessianNormSq (totalPlus s X) = 26 * hessianNormSq X := by
  have hi := innerAction_norm s X hmatrix hbianchi
  have hc := derivativeSlotForm_inner_cross s X hmatrix hbianchi
  have ho := outerAction_norm s X
  rw [totalPlus_inner_outer, hessianNormSq_add, hessianPairing_comm]
  linarith

/-- The plus curvature identity is valid on the entire actual Bianchi
gradient bundle, before taking the highest projection. -/
theorem originalPlusCurvatureForm_eq_of_inner_bianchi (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0) :
    originalPlusCurvatureForm t X = 4 * hessianNormSq X +
      (∑ s, t s * hessianNormSq (totalPlus s X)) / 24 := by
  have h0 := congrArg (fun z : ℝ => t 0 * z)
    (curvature_directional_identity 0 X hmatrix hbianchi)
  have h1 := congrArg (fun z : ℝ => t 1 * z)
    (curvature_directional_identity 1 X hmatrix hbianchi)
  have h2 := congrArg (fun z : ℝ => t 2 * z)
    (curvature_directional_identity 2 X hmatrix hbianchi)
  have htrace := congrArg (fun z : ℝ => 26 * hessianNormSq X * z) ht
  simp only [Fin.sum_univ_three, originalPlusCurvatureForm] at htrace ⊢
  linear_combination (-1 / 24 : ℝ) * (h0 + h1 + h2 + htrace)

/-- This equality includes an unsymmetrized weight tensor as soon as its
inner gradient satisfies Bianchi. The outer slots need not be symmetric. -/
theorem originalCurvatureForm_eq_of_inner_bianchi (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0) :
    originalCurvatureForm t u X = casimirCurvatureForm t u X := by
  rw [originalCurvatureForm,
    originalPlusCurvatureForm_eq_of_inner_bianchi X hmatrix hbianchi t ht,
    minusDerivativeCurvatureForm_eq u hu X]
  unfold casimirCurvatureForm
  ring

private theorem divergence_add_inner (X Y : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (X + Y) i r = divergence X i r + divergence Y i r := by
  have hv (s : Fin 3) :
      (WithLp.toLp 2 (fun j => (X + Y) i j s r) : Vec) =
        WithLp.toLp 2 (fun j => X i j s r) + WithLp.toLp 2 (fun j => Y i j s r) := by
    ext j
    rfl
  simp only [divergence, hv, quaternion_add, Finset.sum_add_distrib]

/-- Polarization of the original real quadratic curvature contraction. -/
def originalPolarPairing (t u : Fin 3 → ℝ) (X Y : Hessian) : ℝ :=
  (originalCurvatureForm t u (X + Y) - originalCurvatureForm t u X -
    originalCurvatureForm t u Y) / 2

theorem casimirCurvatureForm_add (t u : Fin 3 → ℝ) (X Y : Hessian) :
    casimirCurvatureForm t u (X + Y) = casimirCurvatureForm t u X +
      2 * curvaturePairing t u X Y + casimirCurvatureForm t u Y := by
  rw [← curvaturePairing_self, curvaturePairing_add_left]
  simp only [curvaturePairing_add_right, curvaturePairing_self]
  rw [curvaturePairing_comm t u Y X]
  ring

/-- The mixed original curvature term agrees with the computed operator
on arbitrary two inner-Bianchi tensors, including unsymmetrized weights. -/
theorem originalPolarPairing_eq_of_inner_bianchi (X Y : Hessian)
    (hmatrixX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchiX : ∀ i r, divergence X i r = 0)
    (hmatrixY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbianchiY : ∀ i r, divergence Y i r = 0)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0) :
    originalPolarPairing t u X Y = curvaturePairing t u X Y := by
  have hmatrix (i j : Fin 4) : symmetric ((X + Y) i j) ∧ traceFree ((X + Y) i j) := by
    constructor
    · intro a b
      change X i j a b + Y i j a b = X i j b a + Y i j b a
      rw [(hmatrixX i j).1 a b, (hmatrixY i j).1 a b]
    · change (∑ a : Fin 3, (X i j a a + Y i j a a)) = 0
      rw [Finset.sum_add_distrib, (hmatrixX i j).2, (hmatrixY i j).2]
      ring
  have hbianchi (i : Fin 4) (r : Fin 3) : divergence (X + Y) i r = 0 := by
    rw [divergence_add_inner, hbianchiX, hbianchiY, add_zero]
  rw [originalPolarPairing,
    originalCurvatureForm_eq_of_inner_bianchi (X + Y) hmatrix hbianchi t u ht hu,
    originalCurvatureForm_eq_of_inner_bianchi X hmatrixX hbianchiX t u ht hu,
    originalCurvatureForm_eq_of_inner_bianchi Y hmatrixY hbianchiY t u ht hu,
    casimirCurvatureForm_add]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
