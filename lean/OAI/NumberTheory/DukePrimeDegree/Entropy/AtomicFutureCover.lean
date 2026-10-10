import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralPatchFuturePair

namespace OAI

/-! # A full-measure countable neutral future cover from atomic intrinsic roots -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_atomic_neutral_future_cover (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (Q H : X (d+1) → ℕ) (hH : Measurable H)
    (r : ℕ → ℝ) (hanti : Antitone r) (hr : ∀ m, 0 < r m ∧ r m ≤ 1)
    (hinj : ∀ x, LocalInjectivityAt (r (H x)) x)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall (d+1) (r (H x)), rightAction x g=y ∧
        ∀ i j, ell j < ell i → g.val i j=0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (z₀ : NeutralCoordinateBase (d+1) × transverseNeutralSpace (d+1))
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ E : ℕ → Set (X (d+1)), (∀ i, MeasurableSet (E i)) ∧
      (∀ᵐ x ∂μ, x ∈ ⋃ i, E i) ∧
      ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
        fullFutureObservation
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
        fullFutureObservation
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  classical
  choose P hP using fun m => exists_countable_small_neutral_patches (d+1) z₀ (hr m).1
  choose F hF hunique hfull using fun m j =>
    (P m j).exists_atomic_graph μ s hsm hs hA η K₀ hK₀ hηK₀ hatom
  let G (m j : ℕ) := neutralQuotientParam (d+1) (P m j).center ''
    (((P m j).base ×ˢ (P m j).neutral) ∩ Prod.fst ⁻¹' F m j)
  have hG (m j : ℕ) : MeasurableSet (G m j) := by
    apply neutralQuotientParam_measurable_image
    · exact ((P m j).base_open.measurableSet.prod
        (P m j).neutral_open.measurableSet).inter ((hF m j).preimage measurable_fst)
    · exact (neutralQuotientParam_injOn (d+1) (P m j).center (P m j).box _
        (P m j).in_box).mono inter_subset_left
  let E (k : ℕ) := G k.unpair.1 k.unpair.2 ∩ {x | H x ≤ k.unpair.1}
  have hgood : ∀ᵐ x ∂μ, ∀ m j, x ∈ (P m j).raw → x ∈ G m j :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun j => hfull m j
  refine ⟨E,?_,?_,?_⟩
  · intro k
    exact (hG _ _).inter (hH measurableSet_Iic)
  · filter_upwards [hgood] with x hx
    have hxP : x ∈ ⋃ j, (P (H x) j).raw := by rw [hP]; trivial
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    apply mem_iUnion.mpr
    refine ⟨Nat.pair (H x) j,?_⟩
    simpa only [E,Nat.unpair_pair,Set.mem_inter_iff,Set.mem_ofPred_eq] using And.intro (hx (H x) j hj) (le_refl (H x))
  · intro k x hx y hy hobs
    exact (P k.unpair.1 k.unpair.2).graph_future_pair ell hell hord Q
      (fun x => r (H x)) (fun x => (hr (H x)).2) hinj hlift
      (F k.unpair.1 k.unpair.2) (hunique _ _) x y hx.1 hy.1
      (hanti hx.2) hobs

end DukePrimeDegree

end

end OAI
