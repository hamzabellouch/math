import OAI.NumberTheory.DukePrimeDegree.Entropy.ShiftedFactorConditionals

namespace OAI

/-! # Projective constancy of root factors in the remaining-group charts -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem initialRootChart_shifted_leaves_constant
    (d : ℕ) (q : InitialRootStep (d+1)) {k : Fin (d+1)}
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice q.root.1 q.root.2 k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2 + τ z.1)))
    (base : T → X (d+1))
    (factor : B → positiveRootGeneratedGroup (q.remaining.erase q.root))
    (hparam : ∀ s w t, rootQuotientParametrization q.distinct (e (s,w),t) =
      rightAction (base s) ((factor w).val *
        Matrix.SpecialLinearGroup.transvection q.distinct (t - τ (s,w)))) :
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      ∀ᵐ w ∂(σ.condKernel s).fst, ∀ J : Set ℝ,
        anchorNormalize ((A.leafMeasure R μ (e (s,w))).map
          (Homeomorph.addRight (-τ (s,w)))) J = anchorNormalize ν J := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx _ _ q.distinct
  obtain ⟨N,_hN,hN0,hhol⟩ := exists_nullset_shifted_initial_root_leaves d μ hA
  have havoid : ∀ᵐ x ∂μ, x ∉ N := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using hN0
  let F := A.leafMeasure R μ
  let P : RootSlice q.root.1 q.root.2 k × ℝ → Prop := fun z =>
    A.IsNormalizedRootLeaf R μ z.1 (F z.1) ∧
    0 < F z.1 (Metric.ball z.2 1) ∧
    intrinsicRootLeaf q.distinct μ (rootQuotientParametrization q.distinct z) =
      basedRealMeasure (F z.1) z.2 ∧
    rootQuotientParametrization q.distinct z ∉ N
  have hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z := by
    have hs := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
    filter_upwards [hs,A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_coordinate_of_ambient μ havoid] with z hz hp hb hn
    exact ⟨hz,hp 1 zero_lt_one,hb,hn⟩
  filter_upwards [factorChart_shifted_ae_nested q.distinct A μ σ e he τ hτ hcoord hP] with s hs
  obtain ⟨w₀,hw₀⟩ := hs.exists
  obtain ⟨t₀,ht₀⟩ := hw₀.exists
  let ν := F (e (s,w₀))
  have hν : IsLocallyFiniteMeasure ν := ht₀.1.1
  let : IsLocallyFiniteMeasure ν := hν
  refine ⟨ν.map (Homeomorph.addRight (-τ (s,w₀))),
    translatedRealMeasure_locallyFinite ν _,?_⟩
  filter_upwards [hs] with w hw
  obtain ⟨t,ht⟩ := hw.exists
  let ρ := F (e (s,w))
  have hρ : IsLocallyFiniteMeasure ρ := ht.1.1
  have H := hhol q (base s) (factor w₀) (factor w)
    (t₀ + τ (s,w₀)) (t + τ (s,w)) (-τ (s,w₀)) (-τ (s,w)) ν ρ
    hν hρ ht₀.2.1 ht.2.1
  have hp₀ := ht₀.2.2.2
  have hp := ht.2.2.2
  have hb₀ := ht₀.2.2.1
  have hb := ht.2.2.1
  change rootQuotientParametrization q.distinct (e (s,w₀),t₀ + τ (s,w₀)) ∉ N at hp₀
  change rootQuotientParametrization q.distinct (e (s,w),t + τ (s,w)) ∉ N at hp
  change intrinsicRootLeaf q.distinct μ
    (rootQuotientParametrization q.distinct (e (s,w₀),t₀ + τ (s,w₀))) = _ at hb₀
  change intrinsicRootLeaf q.distinct μ
    (rootQuotientParametrization q.distinct (e (s,w),t + τ (s,w))) = _ at hb
  simp only [hparam,sub_eq_add_neg] at hp₀ hp hb₀ hb
  intro J
  exact (H hp₀ hp hb₀ hb J).symm

end DukePrimeDegree

end

end OAI
