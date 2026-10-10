import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoupledRootIntervals
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GoodSourceBundleImage
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # The actual bundle conjugations preserve joint Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]

def innerContinuousMulEquiv (k : N) : N ≃ₜ* N where
  toMulEquiv := MulAut.conj k
  continuous_toFun := IsTopologicalGroup.continuous_conj k
  continuous_invFun := by
    change Continuous (fun u : N => k⁻¹ * u * k)
    simpa only [inv_inv] using (IsTopologicalGroup.continuous_conj k⁻¹)

@[simp] theorem innerContinuousMulEquiv_apply (k u : N) :
    innerContinuousMulEquiv k u = k * u * k⁻¹ := rfl

variable [MeasurableSpace N] [BorelSpace N]

theorem measurePreserving_innerContinuousMulEquiv
    (μ : Measure N) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (k : N) :
    MeasurePreserving (innerContinuousMulEquiv k) μ μ :=
  (measurePreserving_mul_right μ k⁻¹).comp (measurePreserving_mul_left μ k)

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
def bundleConjugator {h : ℕ} (m : ℕ) (k : Fin h → N) (j : ℕ) : N :=
  if hj : j < h * m then k (finProdFinEquiv.symm ⟨j, hj⟩).1 else 1

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
@[simp] theorem bundleConjugator_apply {h m : ℕ} (k : Fin h → N)
    (i : Fin h) (j : Fin m) :
    bundleConjugator m k (finProdFinEquiv (i, j)).val = k i := by
  rw [bundleConjugator, dite_eq_left (finProdFinEquiv (i, j)).isLt]
  change k (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 = k i
  rw [Equiv.symm_apply_apply]

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
theorem bundleConjugator_mem {h m : ℕ} (k : Fin h → N) {S : Set N}
    (h1 : (1 : N) ∈ S) (hk : ∀ i, k i ∈ S) (j : ℕ) : bundleConjugator m k j ∈ S := by
  unfold bundleConjugator
  split_ifs
  · exact hk _
  · exact h1

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
theorem coupledRootIntervalSample_bundle (Exp : L → N) {h m : ℕ}
    (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r : ℝ) (k : Fin h → N)
    (i : Fin h) (j : Fin m) (t : ℝ) :
    coupledRootIntervalSample Exp
      (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2) X s r
      (bundleConjugator m k) (finProdFinEquiv (i, j)).val t =
      k i * Exp (t • (Real.exp (r * s (letters j)) • X (letters j))) * (k i)⁻¹ := by
  dsimp only [coupledRootIntervalSample]
  rw [bundleConjugator_apply, rootIntervalSample_letter]
  simp only [Equiv.symm_apply_apply]

section Lie

open Filter Metric
open scoped Manifold Topology

variable {L₀ I₀ EN : Type*} [LieRing L₀] [LieAlgebra ℝ L₀]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [ChartedSpace EN N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [T2Space N] [SecondCountableTopology N]

omit [T2Space N] in
/-- The second-sheet conjugations are the actual inner automorphisms.
The joint lower volume is retained when passing to all successive states. -/
theorem good_coupled_source_bundle_image {h m : ℕ}
    (lie : L₀ ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
    (X : I₀ → L₀) (s : I₀ → ℝ) (letters : Fin m → I₀)
    (scale : ℕ → ℝ) (p : ℝ)
    (μ : Measure N) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (k : ℕ → Fin h → N) (Good : ℕ → Set N) (x : ℕ → N)
    (hx : ∀ n, x n ∈ Good n) (C : ℕ → Set (Fin h → N))
    (hC : ∀ n, IsCompact (C n))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi fun _ : Fin h => μ) (C n)).toReal / Real.exp (scale n * p)))
    (ρ : ℝ)
    (hreach : ∀ᶠ n in atTop, ∀ y ∈ C n, ∃ t : Fin (h * m + h * m) → ℝ,
      t ∈ closedBall 0 ρ ∧
      SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
        (sampledSwitchParameters
          (coupledRootIntervalSample (Exp ∘ lie)
            (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
            X s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
      sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale n) t = y) :
    let S := fun n => sourceBundleStateEquiv h (x n)
      (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv) '' C n
    (∀ n, IsCompact (S n)) ∧
      HasSubexponentialLowerBoundSeq scale (fun n =>
        ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * p)) ∧
      ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
        ∃ t : Fin (h * m + h * m) → ℝ, t ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
            (sampledSwitchParameters
              (coupledRootIntervalSample (Exp ∘ lie)
                (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
                X s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
          v = sourceBundleStateEquiv h (x n)
            (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale n) t) := by
  apply good_source_bundle_image lie Exp X s letters scale p μ
    (fun n i => innerContinuousMulEquiv (k n i))
    (fun n i => measurePreserving_innerContinuousMulEquiv μ (k n i))
    (fun n => coupledRootIntervalSample (Exp ∘ lie)
      (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
      X s (scale n) (bundleConjugator m (k n)))
    ?_ ?_ Good x hx C hC hvol ρ hreach
  · intro n j u v
    apply coupledRootIntervalSample_sub
    · intro z
      simp only [Function.comp_apply, map_neg, hExp.map_neg]
    · intro z a b
      simpa only [Function.comp_apply, map_smul] using hExp.map_add_smul (lie z) a b
  · intro n i j t
    simpa only [innerContinuousMulEquiv_apply, Function.comp_apply] using
      coupledRootIntervalSample_bundle (Exp ∘ lie) letters X s (scale n) (k n) i j t

end Lie

end PolycyclicRecognition

end

end OAI
