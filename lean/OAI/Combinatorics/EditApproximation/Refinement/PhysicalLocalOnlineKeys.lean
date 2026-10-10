import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalOnlineEquality
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramLaw
import OAI.Combinatorics.EditApproximation.Probability.FiniteKeyRestriction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem physicalScaleIndex_get (N b : ℕ) (hb : b ∈ dyadicScales N) :
    (dyadicScales N).get (physicalScaleIndex N b hb) = b :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)

section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

def physicalOnlineRawKey
    (key : PhysicalOnlineKey source target U N P F A) :
    PhysicalLocalOnlineKey M J N target.length :=
  (key.1, physicalScaleIndex N
      ((stageRepresentatives source target U N P F A key.1.1).get key.2).1
      (representativeList_scale_mem _ _ (List.get_mem _ key.2)),
    ((stageRepresentatives source target U N P F A key.1.1).get key.2).2)

theorem physicalOnlineRawKey_injective :
    Function.Injective (physicalOnlineRawKey source target U N P F A) := by
  rintro ⟨node, representative⟩ ⟨node', representative'⟩ heq
  have hnode := congrArg Prod.fst heq
  change node = node' at hnode
  subst node'
  have hscale := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length =>
    (dyadicScales N).get key.2.1) heq
  have hcenter := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length => key.2.2) heq
  simp only [physicalOnlineRawKey, physicalScaleIndex_get] at hscale hcenter
  have hrep := (representativeList_nodup N P F _ _).injective_get (Prod.ext hscale hcenter)
  cases hrep
  rfl

def physicalLocalOnlineBandG (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) : ℕ :=
  keyedOnlineBandG source target (physicalSourceInterval source.length key.1.1)
    P exponent H ((dyadicScales N).get key.2.1) tau
    (physicalLocalChildMass source target U N P F A T key.1.1 key.1.2) key.2.2

theorem physicalLocalOnlineBandG_positive (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    0 < physicalLocalOnlineBandG source target U N P F A T exponent H tau key :=
  keyedOnlineBandG_positive _ _ _ _ _ _ _ _ _ _

theorem physicalLocalOnlineBandG_on_key (T exponent H : ℕ) (tau : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (key : PhysicalOnlineKey source target U N P F A) :
    physicalLocalOnlineBandG source target U N P F A T exponent H tau
        (physicalOnlineRawKey source target U N P F A key) =
      physicalProgramBandG source target U N P F A T exponent H tau key.1 key.2 := by
  have hmass : physicalLocalChildMass source target U N P F A T key.1.1 key.1.2 =
      physicalBandChildMassTable source target U N P F A T key.1.1 key.1.2 := by
    funext i r
    exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
      (physicalChild key.1.1 key.1.2 i, r)
  simp only [physicalLocalOnlineBandG, physicalOnlineRawKey, physicalScaleIndex_get, hmass,
    keyedOnlineBandG, physicalProgramBandG, physicalBandActions]

def physicalLocalOnlineMass (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) : ℕ :=
  optimizerTriangularMass
    (physicalLocalOnlineBandG source target U N P F A T exponent H tau key ^ 80)

instance physicalLocalOnlineMass_nezero (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    NeZero (physicalLocalOnlineMass source target U N P F A T exponent H tau key) :=
  ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
    (pow_pos (physicalLocalOnlineBandG_positive source target U N P F A T exponent H tau key) 80))⟩

theorem physicalLocalOnlineMass_on_key (T exponent H : ℕ) (tau : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (key : PhysicalOnlineKey source target U N P F A) :
    physicalLocalOnlineMass source target U N P F A T exponent H tau
        (physicalOnlineRawKey source target U N P F A key) =
      optimizerTriangularMass
        (physicalProgramBandK source target U N P F A T exponent H tau key.1 key.2) := by
  unfold physicalLocalOnlineMass physicalProgramBandK
  rw [physicalLocalOnlineBandG_on_key source target U N P F A T exponent H tau
    hsize hP hF hA hseed key]

abbrev PhysicalLocalOnlineDraw (R T exponent H : ℕ) (tau : ℚ) :=
  ∀ key : PhysicalLocalOnlineKey M J N target.length,
    Fin R → Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau key)

noncomputable def physicalLocalOnlineDrawLaw (R T exponent H : ℕ) (tau : ℚ) :
    Measure (PhysicalLocalOnlineDraw source target U N P F A R T exponent H tau) :=
  Measure.pi fun key => Measure.pi fun _ : Fin R =>
    (PMF.uniformOfFintype
      (Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau key))).toMeasure

/-- The bounded-key independent arrays restrict to the original online
coordinates with exactly their prescribed finite uniform laws. -/
theorem physicalLocalOnlineDrawLaw_restrict (R T exponent H : ℕ) (tau : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2) :
    (physicalLocalOnlineDrawLaw source target U N P F A R T exponent H tau).map
      (fun draw (key : PhysicalOnlineKey source target U N P F A) t =>
        Fin.cast (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau
          hsize hP hF hA hseed key)
          (draw (physicalOnlineRawKey source target U N P F A key) t)) =
      Measure.pi (fun key : PhysicalOnlineKey source target U N P F A =>
        Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin (optimizerTriangularMass
          (physicalProgramBandK source target U N P F A T exponent H tau key.1 key.2)))).toMeasure)) := by
  exact finite_uniform_arrays_restrict_cast R _ _
    (physicalOnlineRawKey source target U N P F A)
    (physicalOnlineRawKey_injective source target U N P F A)
    (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed)

end Keys

end EditApproximation

end OAI
