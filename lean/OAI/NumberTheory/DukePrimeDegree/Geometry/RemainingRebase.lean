import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixGroupLeaves
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootBasedMeasure

namespace OAI

/-! # Rebasing a remaining-subgroup leaf at its current coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingRebase (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) : c.Time ≃ₜ c.Time :=
  (c.remainingWordHomeomorph hP hfinal).trans
    ((Homeomorph.mulLeft (c.remainingWordHomeomorph hP hfinal t)⁻¹).trans
      (c.remainingWordHomeomorph hP hfinal).symm)

lemma remainingRebase_word (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t u : c.Time) :
    c.remainingWordHomeomorph hP hfinal (c.remainingRebase hP hfinal t u) =
      (c.remainingWordHomeomorph hP hfinal t)⁻¹ * c.remainingWordHomeomorph hP hfinal u :=
  (c.remainingWordHomeomorph hP hfinal).apply_symm_apply _

lemma continuous_remainingRebase (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Continuous (fun z : c.Time × c.Time => c.remainingRebase hP hfinal z.1 z.2) :=
  (c.remainingWordHomeomorph hP hfinal).symm.continuous.comp
    (((c.remainingWordHomeomorph hP hfinal).continuous.comp continuous_fst).inv.mul
      ((c.remainingWordHomeomorph hP hfinal).continuous.comp continuous_snd))

lemma remainingWord_zero (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.remainingWordHomeomorph hP hfinal c.zeroTime = 1 := by
  apply Subtype.ext
  exact c.word_zeroTime

lemma remainingRebase_self (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.remainingRebase hP hfinal t t = c.zeroTime := by
  apply (c.remainingWordHomeomorph hP hfinal).injective
  rw [c.remainingRebase_word,inv_mul_cancel,c.remainingWord_zero hP hfinal]

lemma remainingRebase_cocycle (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t u v : c.Time) :
    c.remainingRebase hP hfinal (c.remainingRebase hP hfinal t u)
      (c.remainingRebase hP hfinal t v) = c.remainingRebase hP hfinal u v := by
  apply (c.remainingWordHomeomorph hP hfinal).injective
  simp only [c.remainingRebase_word]
  group

def centeredRemainingMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) (t : c.Time) :
    Measure c.Time := ν.map (c.remainingRebase hP hfinal t)

lemma centeredRemainingMeasure_locallyFinite (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) :
    IsLocallyFiniteMeasure (c.centeredRemainingMeasure hP hfinal ν t) := by
  let E := c.remainingRebase hP hfinal t
  constructor
  intro u
  obtain ⟨V,hu,hV,hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm u)
  refine ⟨E '' V,(E.isOpenMap _ hV).mem_nhds ⟨E.symm u,hu,E.apply_symm_apply u⟩,?_⟩
  change ν.map E (E '' V) < ⊤
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hV).measurableSet,
    E.injective.preimage_image]
  exact hfin

lemma centeredRemainingMeasure_unit_pos (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) (t : c.Time) (ht : t ∈ ν.support) :
    0 < c.centeredRemainingMeasure hP hfinal ν t (c.cube 1) := by
  rw [centeredRemainingMeasure,Measure.map_apply (c.remainingRebase hP hfinal t).measurable
    (c.cube_open 1).measurableSet]
  apply (ν.mem_support_iff_forall t).mp ht
  apply IsOpen.mem_nhds ((c.cube_open 1).preimage (c.remainingRebase hP hfinal t).continuous)
  rw [Set.mem_preimage,c.remainingRebase_self]
  exact c.zeroTime_mem_cube zero_lt_one

def basedRemainingMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) (t : c.Time) :
    Measure c.Time := anchorNormalize (c.centeredRemainingMeasure hP hfinal ν t) (c.cube 1)

lemma basedRemainingMeasure_unit (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) (ht : t ∈ ν.support) :
    c.basedRemainingMeasure hP hfinal ν t (c.cube 1) = 1 := by
  let : IsLocallyFiniteMeasure (c.centeredRemainingMeasure hP hfinal ν t) :=
    c.centeredRemainingMeasure_locallyFinite hP hfinal ν t
  have hpos := c.centeredRemainingMeasure_unit_pos hP hfinal ν t ht
  have hfin : c.centeredRemainingMeasure hP hfinal ν t (c.cube 1) < ∞ :=
    (measure_mono (c.cube_subset_closedCube 1)).trans_lt (c.closedCube_compact 1).measure_lt_top
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

lemma basedRemainingMeasure_locallyFinite (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) (ht : t ∈ ν.support) :
    IsLocallyFiniteMeasure (c.basedRemainingMeasure hP hfinal ν t) := by
  let : IsLocallyFiniteMeasure (c.centeredRemainingMeasure hP hfinal ν t) :=
    c.centeredRemainingMeasure_locallyFinite hP hfinal ν t
  have hpos := c.centeredRemainingMeasure_unit_pos hP hfinal ν t ht
  constructor
  intro u
  obtain ⟨U,hu,hU,hfin⟩ :=
    Measure.exists_isOpen_measure_lt_top (c.centeredRemainingMeasure hP hfinal ν t) u
  refine ⟨U,hU.mem_nhds hu,?_⟩
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hpos) hfin

end EliminationChain
end DukePrimeDegree

end

end OAI
