import OAI.NumberTheory.DukePrimeDegree.Geometry.CommutatorInvariance
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootInvariantLeaves

namespace OAI

/-!
# Measure preservation of the three-root shear

For the root-order change in EK2003, Proposition 8.3, a noncommuting pair
adds the product of its parameters to the commutator coordinate. If a
factor is Dirac the shear vanishes. Otherwise commutator invariance makes
the third factor translation invariant.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootProductShear (z : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (z.1,z.2 + z.1.1 * z.1.2)

lemma measurable_rootProductShear : Measurable rootProductShear := by
  unfold rootProductShear
  fun_prop

theorem rootProductShear_preserves (ν η κ : Measure ℝ) [SFinite ν] [SFinite η] [SFinite κ]
    (h : ν = Measure.dirac 0 ∨ η = Measure.dirac 0 ∨
      ∀ a : ℝ, κ.map (fun t => t + a) = κ) :
    ((ν.prod η).prod κ).map rootProductShear = (ν.prod η).prod κ := by
  rcases h with h | h | h
  · have hz : ∀ᵐ z ∂(ν.prod η).prod κ, z.1.1 = 0 := by
      rw [Measure.ae_prod_iff_ae_ae (isClosed_eq (continuous_fst.fst) continuous_const).measurableSet]
      have hf : ∀ᵐ w ∂ν.prod η, w.1 = 0 := by
        rw [Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_const).measurableSet,h]
        simp
      exact hf.mono fun _ hw => ae_of_all _ fun _ => hw
    calc
      _ = ((ν.prod η).prod κ).map id := Measure.map_congr (hz.mono fun z hz => by
        simp [rootProductShear,hz])
      _ = _ := Measure.map_id
  · have hz : ∀ᵐ z ∂(ν.prod η).prod κ, z.1.2 = 0 := by
      rw [Measure.ae_prod_iff_ae_ae (isClosed_eq (continuous_fst.snd) continuous_const).measurableSet]
      have hf : ∀ᵐ w ∂ν.prod η, w.2 = 0 := by
        rw [Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_snd continuous_const).measurableSet,h]
        simp
      exact hf.mono fun _ hw => ae_of_all _ fun _ => hw
    calc
      _ = ((ν.prod η).prod κ).map id := Measure.map_congr (hz.mono fun z hz => by
        simp [rootProductShear,hz])
      _ = _ := Measure.map_id
  · exact ((MeasurePreserving.id (ν.prod η)).skew_product
      (show Measurable (fun z : (ℝ × ℝ) × ℝ => z.2 + z.1.1 * z.1.2) by fun_prop)
      (ae_of_all _ fun z => h (z.1 * z.2))).map_eq

theorem ae_intrinsic_rootProductShear_preserves
    (d : ℕ) {a b c : Fin (d+1)} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ,
      (((intrinsicRootLeaf hab μ x).prod (intrinsicRootLeaf hbc μ x)).prod
        (intrinsicRootLeaf hac μ x)).map rootProductShear =
      ((intrinsicRootLeaf hab μ x).prod (intrinsicRootLeaf hbc μ x)).prod
        (intrinsicRootLeaf hac μ x) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree (i j : Fin (d+1)) (hij : i ≠ j) : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx i j hij
  have hs := (ae_intrinsicRootLeaf_spec hab μ (hfree _ _ hab)).and
    ((ae_intrinsicRootLeaf_spec hbc μ (hfree _ _ hbc)).and
      (ae_intrinsicRootLeaf_spec hac μ (hfree _ _ hac)))
  have hcases : ∀ᵐ x ∂μ,
      intrinsicRootLeaf hab μ x = Measure.dirac 0 ∨
      intrinsicRootLeaf hbc μ x = Measure.dirac 0 ∨
      ∀ t : ℝ, (intrinsicRootLeaf hac μ x).map (fun r => r+t) = intrinsicRootLeaf hac μ x := by
    rcases intrinsicRootLeaf_ergodic_alternative d hab μ with ha | ha
    · rcases intrinsicRootLeaf_ergodic_alternative d hbc μ with hb | hb
      · have hi := root_invariant_of_adjacent_nonatomic_leaves d hab hbc hac μ ha hb
        exact (ae_rootLeaf_invariant_of_root_invariant d hac μ hA hi).mono fun _ hx =>
          Or.inr (Or.inr hx)
      · exact hb.mono fun _ hx => Or.inr (Or.inl hx)
    · exact ha.mono fun _ hx => Or.inl hx
  filter_upwards [hs,hcases] with x hx hc
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hab μ x) := hx.1.1
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hbc μ x) := hx.2.1.1
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hac μ x) := hx.2.2.1
  exact rootProductShear_preserves _ _ _ hc

end DukePrimeDegree

end

end OAI
