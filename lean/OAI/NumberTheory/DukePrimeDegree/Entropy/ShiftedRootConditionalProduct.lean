import OAI.NumberTheory.DukePrimeDegree.Geometry.ShiftedRootProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.RestrictedLeafProduct

namespace OAI

/-!
# The remaining-root product law on physical time windows

The canonical one-root chart uses a time origin depending on all transverse
coordinates. Removing that origin before restricting gives the product step
in the ordered-root induction of EK2003, Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem initialRootChart_shifted_conditional_product
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
        Matrix.SpecialLinearGroup.transvection q.distinct (t - τ (s,w))))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      (Homeomorph.addRight (τ (s,w))) '' J ⊆ A.time) :
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx _ _ q.distinct
  have hnorm : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.IsNormalizedRootLeaf R μ z.1 (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  have hs := factorChart_shifted_ae_nested q.distinct A μ σ e he τ hτ hcoord hnorm
  have hc := factorChart_shifted_nested_conditionals q.distinct A μ σ e he τ hτ hcoord
  have hp := initialRootChart_shifted_leaves_constant d q A R hAR μ hA σ e he τ hτ
    hcoord base factor hparam
  filter_upwards [hs,hc,hp,hwindow] with s hsn hsc hsp hsw
  obtain ⟨ν,_hν,heq⟩ := hsp
  refine ⟨(anchorNormalize ν J).restrict J,anchorNormalize_restrict_finite ν J,?_⟩
  apply restricted_eq_prod_of_projective_leaf_restrictions (σ.condKernel s) J hJ
    (fun w => (A.leafMeasure R μ (e (s,w))).map (Homeomorph.addRight (-τ (s,w)))) ν
  · filter_upwards [hsn,hsc,hsw] with w hwn hwc hww
    obtain ⟨t,ht⟩ := hwn.exists
    have hk : ((σ.condKernel s).condKernel w).map (Homeomorph.addRight (τ (s,w))) =
        (A.leafMeasure R μ (e (s,w))).restrict A.time :=
      hwc.symm.trans ht.2.2.1.symm
    have H := shifted_leaf_restrict (A.leafMeasure R μ (e (s,w)))
      ((σ.condKernel s).condKernel w) A.time J hJ (τ (s,w)) hww hk
    have hequiv : (Homeomorph.addRight (τ (s,w))).symm = Homeomorph.addRight (-τ (s,w)) := by
      ext x
      rfl
    rw [hequiv] at H
    exact H.symm
  · exact heq.mono fun _ hw => hw J

end DukePrimeDegree

end

end OAI
