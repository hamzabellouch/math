import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootHopf
import Mathlib.Probability.Kernel.MeasurableIntegral

namespace OAI

/-!
# Neutral root leaves are constant along contracting root fibers

Bounded transforms let the scalar Hopf theorem apply to every measurable
leaf-test integral. The countable determining family for locally finite
real measures then gives equality of the leaf kernels themselves.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_rootBox_eq_of_measurable_diagonal_invariant
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hweight : ell i - ell j = 1)
    (μ : Measure (X n)) [IsFiniteMeasure μ] [μ.Regular]
    (B : RootBox hij k)
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    (f : X n → ℝ) (hf : Measurable f)
    (hfinv : (fun x => f (rightAction x (diagonalOneParameter ell hell 1))) =ᵐ[μ] f) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      f (rootQuotientParametrization hij z) =
        f (rootQuotientParametrization hij (z.1, t)) := by
  have hint : Integrable (fun x => Real.arctan (f x)) μ := by
    apply (integrable_const (Real.pi / 2)).mono'
      ((Real.continuous_arctan.measurable.comp hf).aestronglyMeasurable)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hi : (fun x => Real.arctan (f (rightAction x (diagonalOneParameter ell hell 1)))) =ᵐ[μ]
      fun x => Real.arctan (f x) := hfinv.mono fun _ h => congrArg Real.arctan h
  have h := ae_rootBox_eq_of_diagonal_invariant hij ell hell hweight μ B hT
    (fun x => Real.arctan (f x)) hint hi
  filter_upwards [h] with z hz
  exact hz.mono fun t ht => Real.arctan_injective ht

/-- A neutral diagonal direction preserves a root kernel almost everywhere. -/
theorem ae_intrinsicRootKernel_neutral
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneutral : ell i = ell j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree
      (rightAction x (diagonalOneParameter ell hell t)) = intrinsicRootKernel hij μ hfree x := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell t)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have he := ae_intrinsicRootKernel_eq hij μ hfree
  have heT : ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree (T x) = intrinsicRootLeaf hij μ (T x) :=
    ae_of_ae_map hT.measurable.aemeasurable (by rwa [hT.map_eq])
  filter_upwards [he, heT, ae_rootLeaf_neutral_diagonal d hij ell hell hneutral μ hA t]
    with x hx hTx hn
  exact hTx.trans (hn.trans hx.symm)

/-- Countably many leaf tests identify the kernel on a contracting root fiber. -/
theorem ae_rootBox_intrinsicKernel_eq
    (d : ℕ) {i j k l p : Fin (d + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0)
    (hneutral : ell i = ell j) (hweight : ell k - ell l = 1)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ] [μ.Regular]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (B : RootBox hkl p) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      intrinsicRootKernel hij μ hfree (rootQuotientParametrization hkl z) =
        intrinsicRootKernel hij μ hfree (rootQuotientParametrization hkl (z.1, t)) := by
  let κ := intrinsicRootKernel hij μ hfree
  have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hinv := ae_intrinsicRootKernel_neutral d hij ell hell hneutral μ hA hfree 1
  have htest (N q : ℕ) : ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      (∫ u, leafTest N q u ∂κ (rootQuotientParametrization hkl z)) =
        ∫ u, leafTest N q u ∂κ (rootQuotientParametrization hkl (z.1, t)) := by
    apply ae_rootBox_eq_of_measurable_diagonal_invariant hkl ell hell hweight μ B hT
      (fun x => ∫ u, leafTest N q u ∂κ x)
    · exact (leafTest N q).continuous.stronglyMeasurable.integral_kernel.measurable
    · exact hinv.mono fun x hx => congrArg (fun ν : Measure ℝ => ∫ u, leafTest N q u ∂ν) hx
  have hall : ∀ᵐ z ∂B.coordinateMeasure μ, ∀ N q : ℕ,
      ∀ᵐ t ∂B.conditionalKernel μ z.1,
        (∫ u, leafTest N q u ∂κ (rootQuotientParametrization hkl z)) =
          ∫ u, leafTest N q u ∂κ (rootQuotientParametrization hkl (z.1, t)) :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun q => htest N q
  filter_upwards [hall] with z hz
  have hzt := ae_all_iff.mpr fun N => ae_all_iff.mpr fun q => hz N q
  filter_upwards [hzt] with t ht
  exact (realMeasures_eq_iff_leafTests _ _).mpr ht

/-- The intrinsic leaf itself is unchanged on those same conditional fibers. -/
theorem ae_rootBox_intrinsicLeaf_eq
    (d : ℕ) {i j k l p : Fin (d + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0)
    (hneutral : ell i = ell j) (hweight : ell k - ell l = 1)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ] [μ.Regular]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (B : RootBox hkl p) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hkl z) =
        intrinsicRootLeaf hij μ (rootQuotientParametrization hkl (z.1, t)) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have he := ae_intrinsicRootKernel_eq hij μ hfree
  have hR : Measurable (rootQuotientParametrization (k := p) hkl) :=
    (rootQuotientParametrization_localHomeomorph hkl).continuous.measurable
  have hρ : ∀ᵐ z ∂B.coordinateMeasure μ,
      intrinsicRootKernel hij μ hfree (rootQuotientParametrization hkl z) =
        intrinsicRootLeaf hij μ (rootQuotientParametrization hkl z) := by
    apply ae_of_ae_map hR.aemeasurable
      (p := fun x => intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x)
    rw [B.map_coordinateMeasure]
    exact ae_restrict_of_ae he
  have hp := ae_conditionalPair_of_ambient (B.coordinateMeasure μ) hρ
  have hp' := Measure.ae_ae_of_ae_compProd
    (μ := B.coordinateMeasure μ)
    (κ := (B.coordinateMeasure μ).condKernel.comap Prod.fst measurable_fst) hp
  have hκ := ae_rootBox_intrinsicKernel_eq d hij hkl ell hell hneutral hweight μ hA hfree B
  filter_upwards [hp', hκ] with z hz hkz
  filter_upwards [hz, hkz] with t ht hkt
  exact ht.1.symm.trans (hkt.trans ht.2)

/-- Any nonparallel root admits a neutral contracting direction, so the
intrinsic leaf is constant on its conditional fibers. -/
theorem ae_rootBox_intrinsicLeaf_eq_of_nonparallel
    (d : ℕ) {i j k l p : Fin (d + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (hforward : ¬ (k = i ∧ l = j)) (hbackward : ¬ (k = j ∧ l = i))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ] [μ.Regular]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (B : RootBox hkl p) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hkl z) =
        intrinsicRootLeaf hij μ (rootQuotientParametrization hkl (z.1, t)) := by
  obtain ⟨ell, hell, hn, hw⟩ :=
    exists_neutral_expanding_weights d hij hkl hforward hbackward
  apply ae_rootBox_intrinsicLeaf_eq d hij hkl (fun r => -ell r) _ _ _ μ hA B
  · simp only [Finset.sum_neg_distrib, hell, neg_zero]
  · exact congrArg Neg.neg hn
  · linarith

end DukePrimeDegree

end

end OAI
