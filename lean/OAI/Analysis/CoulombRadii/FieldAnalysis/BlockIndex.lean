import Mathlib
import OAI.Analysis.CoulombRadii.Localization.ConfigSupported

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
noncomputable def blockIndex (m k : ℕ) :
    (Fin m × Fin 3) ⊕ (Fin k × Fin 3) ≃ Fin (m+k) × Fin 3 :=
  (Equiv.sumProdDistrib (Fin m) (Fin k) (Fin 3)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

noncomputable def joinConfiguration (m k : ℕ) :
    (Configuration m × Configuration k) ≃L[ℝ] Configuration (m+k) :=
  EuclideanSpace.sumEquivProd.symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).toContinuousLinearEquiv

lemma joinConfiguration_measurePreserving (m k : ℕ) :
    MeasurePreserving (joinConfiguration m k).toHomeomorph.toMeasurableEquiv
      (volume.prod volume) volume := by
  have h1 := WithLp.volume_preserving_toLp (Configuration m) (Configuration k)
  have h2 := (PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : (Fin m × Fin 3) ⊕ (Fin k × Fin 3) => ℝ)).symm.measurePreserving
  have h3 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).measurePreserving
  exact h3.comp (h2.comp h1)

lemma joinConfiguration_left (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin m) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.castAdd k i,b) = x (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin k) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.natAdd m i,b) = y (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right_single (m k : ℕ) (a : Fin k × Fin 3) :
    joinConfiguration m k (0, EuclideanSpace.single a 1) =
      EuclideanSpace.single (Fin.natAdd m a.1, a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [joinConfiguration_left]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (m+k) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
  · intro j
    rw [joinConfiguration_right]
    simp [PiLp.single_apply, Prod.ext_iff]

lemma joinConfiguration_left_single (m k : ℕ) (a : Fin m × Fin 3) :
    joinConfiguration m k (EuclideanSpace.single a 1, 0) =
      EuclideanSpace.single (Fin.castAdd k a.1, a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [joinConfiguration_left]
    simp [PiLp.single_apply, Prod.ext_iff]
  · intro j
    rw [joinConfiguration_right]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (m+k) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl

lemma joinConfiguration_symm_measurePreserving (m k : ℕ) :
    MeasurePreserving (joinConfiguration m k).symm.toHomeomorph.toMeasurableEquiv
      volume (volume.prod volume) :=
  MeasurePreserving.symm _ (joinConfiguration_measurePreserving m k)

def tensorValue {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (x : Configuration (m+k)) : ℂ :=
  u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 *
    v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2

def tensorGradient {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) (x : Configuration (m+k)) : ℂ :=
  Fin.addCases
    (fun i => u.gradient (s ∘ Fin.castAdd k) (i,a.2) ((joinConfiguration m k).symm x).1 *
      v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2)
    (fun i => u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 *
      v.gradient (s ∘ Fin.natAdd m) (i,a.2) ((joinConfiguration m k).symm x).2) a.1

lemma tensorValue_memLp {m k : ℕ} (u : H1Vector m) (v : H1Vector k) (s : Spins (m+k)) :
    MemLp (tensorValue u v s) 2 volume :=
  (tensorPair_memLp (u.value_L2 _) (v.value_L2 _)).comp_measurePreserving
    (joinConfiguration_symm_measurePreserving m k)

lemma tensorGradient_memLp {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) :
    MemLp (tensorGradient u v s a) 2 volume := by
  rcases a with ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    unfold tensorGradient
    simp only [Fin.addCases_left]
    exact
      (tensorPair_memLp (u.partial_L2 (s ∘ Fin.castAdd k) (j,b)) (v.value_L2 (s ∘ Fin.natAdd m))).comp_measurePreserving
        (joinConfiguration_symm_measurePreserving m k)
  · intro j
    unfold tensorGradient
    simp only [Fin.addCases_right]
    exact
      (tensorPair_memLp (u.value_L2 (s ∘ Fin.castAdd k)) (v.partial_L2 (s ∘ Fin.natAdd m) (j,b))).comp_measurePreserving
        (joinConfiguration_symm_measurePreserving m k)

lemma tensorValue_join {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (z : Configuration m × Configuration k) :
    tensorValue u v s (joinConfiguration m k z) =
      u.value (s ∘ Fin.castAdd k) z.1*v.value (s ∘ Fin.natAdd m) z.2 := by
  simp only [tensorValue, ContinuousLinearEquiv.symm_apply_apply]

lemma tensorGradient_join_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin m × Fin 3) (z : Configuration m × Configuration k) :
    tensorGradient u v s (Fin.castAdd k a.1,a.2) (joinConfiguration m k z) =
      u.gradient (s ∘ Fin.castAdd k) a z.1*v.value (s ∘ Fin.natAdd m) z.2 := by
  simp only [tensorGradient, Fin.addCases_left, ContinuousLinearEquiv.symm_apply_apply]

lemma tensorGradient_join_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin k × Fin 3) (z : Configuration m × Configuration k) :
    tensorGradient u v s (Fin.natAdd m a.1,a.2) (joinConfiguration m k z) =
      u.value (s ∘ Fin.castAdd k) z.1*v.gradient (s ∘ Fin.natAdd m) a z.2 := by
  simp only [tensorGradient, Fin.addCases_right, ContinuousLinearEquiv.symm_apply_apply]

lemma tensor_weak_partial {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3)
    (φ : Configuration (m+k) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ x, tensorValue u v s x*(fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, tensorGradient u v s a x*(φ x : ℂ)) := by
  let : ContinuousSMul ℝ (Configuration m × Configuration k) := Prod.continuousSMul
  let J := joinConfiguration m k
  have hJ := joinConfiguration_measurePreserving m k
  have htest : ContDiff ℝ ∞ (φ ∘ J) := hφ.comp J.contDiff
  have htestC : HasCompactSupport (φ ∘ J) := hC.comp_homeomorph J.toHomeomorph
  have hdtest (z : Configuration m × Configuration k) (b : Configuration m × Configuration k) :
      fderiv ℝ (φ ∘ J) z b = fderiv ℝ φ (J z) (J b) := by
    rw [((hφ.differentiable (by simp) (J z)).hasFDerivAt.comp z J.hasFDerivAt).fderiv]
    rfl
  rw [← hJ.integral_comp' (fun x => tensorValue u v s x*
      (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)),
    ← hJ.integral_comp' (fun x => tensorGradient u v s a x*(φ x : ℂ))]
  change (∫ z : Configuration m × Configuration k,
    tensorValue u v s (joinConfiguration m k z)*
      (fderiv ℝ φ (joinConfiguration m k z) (EuclideanSpace.single a 1) : ℂ)
        ∂(volume.prod volume)) =
    -(∫ z : Configuration m × Configuration k,
      tensorGradient u v s a (joinConfiguration m k z)*
        (φ (joinConfiguration m k z) : ℂ) ∂(volume.prod volume))
  rcases a with ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    have H := tensor_weak_left (u.value_L2 (s ∘ Fin.castAdd k))
      (u.partial_L2 (s ∘ Fin.castAdd k) (j,b)) (v.value_L2 (s ∘ Fin.natAdd m))
      (EuclideanSpace.single (j,b) 1)
      (fun t ht htC => by simpa only [mul_comm] using u.weak_partial _ (j,b) t ht htC)
      (φ ∘ J) htest htestC
    simp_rw [hdtest] at H
    simp only [J, joinConfiguration_left_single, Function.comp_apply] at H
    simp only [tensorValue_join, tensorGradient_join_left u v s (j,b)]
    simpa only [mul_comm] using H
  · intro j
    have H := tensor_weak_right (u.value_L2 (s ∘ Fin.castAdd k))
      (v.value_L2 (s ∘ Fin.natAdd m)) (v.partial_L2 (s ∘ Fin.natAdd m) (j,b))
      (EuclideanSpace.single (j,b) 1)
      (fun t ht htC => by simpa only [mul_comm] using v.weak_partial _ (j,b) t ht htC)
      (φ ∘ J) htest htestC
    simp_rw [hdtest] at H
    simp only [J, joinConfiguration_right_single, Function.comp_apply] at H
    simp only [tensorValue_join, tensorGradient_join_right u v s (j,b)]
    simpa only [mul_comm] using H

def H1Vector.tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : H1Vector (m+k) where
  value := tensorValue u v
  gradient := tensorGradient u v
  value_L2 := tensorValue_memLp u v
  partial_L2 := tensorGradient_memLp u v
  weak_partial := tensor_weak_partial u v
end Coulomb

end

end OAI
