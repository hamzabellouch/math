import OAI.NumberTheory.DukePrimeDegree.Geometry.OwnLeafSeparation

namespace OAI

/-!
# Pointwise separation of root fibers on a conull set

Coordinate disintegration gives one ambient null set outside which the
intrinsic leaf agrees with the chart leaf at every remaining point.
Within a fixed root box, equal leaves at points in one fiber then force
equal points in the noninvariant ergodic case. This strengthens the
conditional-almost-everywhere form needed in EKL (2006), Lemma 4.4(2).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootBox_exists_nullset_for_coordinates
    {n : ℕ} {i j k : Fin n} {hij : i ≠ j}
    (A : RootBox hij k) (μ : Measure (X n))
    (Q : RootSlice i j k × ℝ → Prop)
    (hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, rootQuotientParametrization hij z ∉ N → Q z := by
  have hchart : ∀ᵐ x ∂μ.restrict A.range,
      ∀ z ∈ A.domain, rootQuotientParametrization hij z = x → Q z := by
    apply A.ae_of_coordinate μ
    filter_upwards [hQ, A.coordinateMeasure_ae_domain μ] with z hz hzd
    intro w hw heq
    have he : (⟨w, hw⟩ : A.domain) = ⟨z, hzd⟩ := A.embedding.injective heq
    have he' : w = z := congrArg Subtype.val he
    simpa only [he'] using hz
  have hall := (ae_restrict_iff' A.range_open.measurableSet).mp hchart
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz hx
  by_contra h
  apply hx
  apply hbad
  intro H
  exact h (H ⟨⟨z, hz⟩, rfl⟩ z hz rfl)

theorem rootBox_leaf_separates_fibers_outside_nullset
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ)
    (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, ∀ w ∈ A.domain,
        rootQuotientParametrization hij z ∉ N →
        rootQuotientParametrization hij w ∉ N → z.1 = w.1 →
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) =
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) → z = w := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hsep : ∀ᵐ z ∂A.coordinateMeasure μ, ∀ t : ℝ,
      basedRealMeasure (intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)) t =
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) → t = 0 := by
    have hR : Measurable (rootQuotientParametrization (k := k) hij) :=
      (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
    apply ae_of_ae_map (μ := A.coordinateMeasure μ)
      (p := fun x => ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hij μ x) t =
        intrinsicRootLeaf hij μ x → t = 0) hR.aemeasurable
    rw [A.map_coordinateMeasure]
    exact ae_restrict_of_ae (ae_based_rootLeaf_eq_only_at_zero d hij μ hnot)
  let Q := fun z : RootSlice i j k × ℝ =>
    intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = A.basedLeaf R μ z ∧
    IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) ∧
    0 < A.leafMeasure R μ z.1 (Metric.ball z.2 1) ∧
    ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)) t =
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) → t = 0
  have hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z := by
    have hloc := ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
    filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree, hloc,
      A.ae_leafMeasure_ball_pos R hAR μ hfree, hsep] with z hz hl hp hs
    exact ⟨hz, hl, hp 1 zero_lt_one, hs⟩
  obtain ⟨N, hN, hzero, hgood⟩ := rootBox_exists_nullset_for_coordinates A μ Q hQ
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz w hw hzN hwN hbase heq
  have hgz := hgood z hz hzN
  have hgw := hgood w hw hwN
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hgz.2.1
  have hrebase : basedRealMeasure (intrinsicRootLeaf hij μ (rootQuotientParametrization hij z))
      (w.2 - z.2) = intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) := by
    rw [hgz.1, hgw.1]
    change basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (w.2 - z.2) =
      basedRealMeasure (A.leafMeasure R μ w.1) w.2
    rw [← hbase, basedRealMeasure_rebase _ _ _ hgz.2.2.1]
    congr 1
    ring
  have ht := hgz.2.2.2 (w.2 - z.2) (hrebase.trans heq.symm)
  exact Prod.ext hbase (sub_eq_zero.mp ht).symm

end DukePrimeDegree

end

end OAI
