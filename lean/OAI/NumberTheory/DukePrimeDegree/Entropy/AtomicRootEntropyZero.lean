import OAI.NumberTheory.DukePrimeDegree.Entropy.AtomicFutureCover
import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallFutureObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountablePatchEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorFutureInformation

namespace OAI

/-! # Atomic expanding roots force zero metric entropy -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_entropy_zero_of_atomic_positive_roots (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hA' (v : transverseNeutralSpace (d+1)) :
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hord : StrictMono ell := by
    intro i j hij
    have hh := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  obtain ⟨H,Q,r,hH,hQ,hanti,hr,hinj,hbranch,hlift,hbilateral⟩ :=
    exists_small_future_observation d ell hell hgap μ hA
  obtain ⟨s,hsm,hs⟩ := exists_measurable_quotient_section (d+1)
  let K₀ : PositiveCompacts (transverseNeutralSpace (d+1)) := Classical.arbitrary _
  let η := Measure.addHaarMeasure K₀
  let z₀ : NeutralCoordinateBase (d+1) × transverseNeutralSpace (d+1) :=
    ((⟨upperRootIdentity (d+1),by intro i; simp [upperRootIdentity]⟩,
      (completeRootChain (d+1)).zeroTime),0)
  obtain ⟨E,hE,hfull,hpair⟩ := exists_atomic_neutral_future_cover d ell hell hord Q H hH
    r hanti hr hinj hlift μ s hsm hs hA' η K₀ K₀.isCompact Measure.addHaarMeasure_self
    z₀ hatom
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M,B,decode,hB,href,hdecode,hupper⟩ :=
    finite_predecessors_entropy_upper μ hT Q hQ hbranch
  have hzero := predecessor_information_zero_of_sublinear_words μ hT Q hQ B hB href
    decode hdecode (fun ε hε =>
      countable_patch_name_entropy_sublinear ell hell Q hQ E hE hpair μ hfull hT B hB hε)
  apply le_antisymm _ bot_le
  have hbound := measureEntropy_le_of_bilateral_heightClip_bounds d ell hell Q hQ μ hA
    (fun x y hxy => hbilateral x y hxy.1 hxy.2) 0
    (fun L => by simpa only [hzero] using hupper L)
  simpa only [ENNReal.ofReal_zero,bot_eq_zero] using hbound

end DukePrimeDegree

end

end OAI
