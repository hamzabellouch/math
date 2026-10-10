import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantVersion
import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralWeightSpace

namespace OAI

/-!
# A pointwise neutral-invariant version of the intrinsic leaf data

Neutral diagonal translations have root scaling factor one, so their
actual leaf kernels agree almost everywhere. Haar orbit constants give
a version of the countable determining data invariant under every
neutral translation at every point.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_neutralSpace_rootKernel_eq
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (u : Multiplicative (neutralWeightSpace i j)) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree (rightAction x (neutralSpaceDiagonal i j u)) =
      intrinsicRootKernel hij μ hfree x := by
  have hpres : MeasurePreserving (fun x => rightAction x (neutralSpaceDiagonal i j u)) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    change μ.map (fun x => rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = μ
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hmap : ∀ᵐ y ∂μ.map (fun x => rightAction x (neutralSpaceDiagonal i j u)),
      intrinsicRootKernel hij μ hfree y = intrinsicRootLeaf hij μ y := by
    rw [hpres.map_eq]
    exact ae_intrinsicRootKernel_eq hij μ hfree
  have htarget := ae_of_ae_map hpres.measurable.aemeasurable hmap
  have hcov := ae_intrinsicRootLeaf_diagonal hij u.toAdd.val u.toAdd.property.1 1 μ hfree hpres.map_eq
  have hdiff : u.toAdd.val j - u.toAdd.val i = 0 := sub_eq_zero.mpr u.toAdd.property.2.symm
  have hscale : rootTimeScaling u.toAdd.val i j 1 = Homeomorph.refl ℝ := by
    ext t
    simp [rootTimeScaling, hdiff]
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, htarget, hcov,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hx ht hc hs
  rw [ht, hx]
  change intrinsicRootLeaf hij μ
    (rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = _
  rw [hc, hscale]
  change anchorNormalize ((intrinsicRootLeaf hij μ x).map id) (Metric.ball 0 1) = _
  rw [Measure.map_id]
  simp only [anchorNormalize, hs.2, inv_one, one_smul]

theorem exists_strictly_neutral_invariant_leafData
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ V : X (d + 1) → (ℕ × ℕ → ℝ),
      V =ᵐ[μ] intrinsicLeafData hij μ hfree ∧ AEMeasurable V μ ∧
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        ∀ x, V (rightAction x (diagonalOneParameter ell hell 1)) = V x := by
  let H := Multiplicative (neutralWeightSpace i j)
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let σ : Measure H := Measure.haar
  let R : H → X (d + 1) → X (d + 1) :=
    fun u x => rightAction x (neutralSpaceDiagonal i j u)
  have hR : Measurable (fun p : H × X (d + 1) => R p.1 p.2) := by
    exact ((continuous_rightAction_uncurry (d + 1)).comp
      (continuous_snd.prodMk ((continuous_neutralSpaceDiagonal i j).comp continuous_fst))).measurable
  have hone (x : X (d + 1)) : R 1 x = x := by simp [R]
  have hmul (a b : H) (x : X (d + 1)) : R a (R b x) = R (a * b) x := by
    dsimp only [R]
    rw [rightAction_mul, ← map_mul, mul_comm b a]
  have hinv (a : H) : ∀ᵐ x ∂μ,
      intrinsicLeafData hij μ hfree (R a x) = intrinsicLeafData hij μ hfree x := by
    filter_upwards [ae_neutralSpace_rootKernel_eq d hij μ hA hfree a] with x hx
    exact (intrinsicLeafData_eq_iff hij μ hfree (R a x) x).mpr hx
  obtain ⟨V, heq, hm, hv⟩ := exists_strictly_invariant_version σ μ R hR hone hmul
    (fun b => measurePreserving_mul_right σ b)
    (intrinsicLeafData hij μ hfree) (measurable_intrinsicLeafData hij μ hfree) hinv
  refine ⟨V, heq, hm, ?_⟩
  intro ell hell hn x
  exact hv (Multiplicative.ofAdd (⟨ell, hell, hn⟩ : neutralWeightSpace i j)) x

end DukePrimeDegree

end

end OAI
