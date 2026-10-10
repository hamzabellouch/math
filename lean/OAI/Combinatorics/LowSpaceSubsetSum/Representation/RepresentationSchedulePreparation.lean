import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedFields

namespace OAI

/-! # Constructing the residue-loop schedule from stored arrays -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationSchedulePreparation

variable {n g : ℕ}

abbrev width (n : ℕ) := StoredTopCoordinates.width n

def ofStored (I : Instance n) (d : RepresentationExtraPreparation.Data n)
    (hp : 0 < d.residues.primes.moduli[0]) (hq : 0 < d.q)
    (hr : d.residues.residues[0] < d.residues.primes.moduli[0])
    (hi : Function.Injective (fun p : Fin 4 × Fin (width n) =>
      (d.residues.primes.stored.coordinates p.1)[p.2.val])) : RepresentationScheduleData n (width n) where
  input := I
  signs := d.residues.primes.stored.stored.layout.signs.semantic
  leaves := d.residues.primes.stored.leaves
  lowModuli j := d.residues.primes.moduli[j.val + 1]
  firstResidues j := if j = 0 then (d.residues.residues[1] : ℤ) else d.residues.residues[2]
  p0 := d.residues.primes.moduli[0]
  p0_positive := hp
  q := d.q
  q_positive := hq
  rho0 := ⟨d.residues.residues[0], hr⟩
  capacity := compressionDictionaryCapacity n
  coordinates := ⟨_, hi⟩
  topOrder := (StoredOrderedMixers.lists d.residues.primes.stored.stored.layout)[0]

def fromSuccess (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    RepresentationScheduleData n (width n) :=
  let hs := RepresentationPreparedFields.agrees I hn hlog s d h
  let source := RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog
    (((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s)
  let hp : 0 < d.residues.primes.moduli[0] := hs.p0.symm ▸ source.p0_positive
  let hq : 0 < d.q := hs.q.symm ▸ source.q_positive
  let hr : d.residues.residues[0] < d.residues.primes.moduli[0] := by
    rw [hs.rho0, hs.p0]
    exact source.rho0.isLt
  let hi : Function.Injective (fun p : Fin 4 × Fin (width n) =>
      (d.residues.primes.stored.coordinates p.1)[p.2.val]) := by
    intro a b hab
    apply source.coordinates.injective
    simpa only [hs.coordinates] using hab
  ofStored I d hp hq hr hi

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    Option (RepresentationScheduleData n (width n)) × ℕ :=
  let prepared := RepresentationExtraPreparation.run I hn hlog s
  match h : prepared.1 with
  | none => (none, prepared.2 + 1)
  | some d => (some (fromSuccess I hn hlog s d h), prepared.2 + 16)

theorem coordinates_ext {P Q : TopCoordinates n g} (h : P.index = Q.index) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem ofStored_eq (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (history : (canonicalRepresentationData I).zeroSetup.ExtraTrialHistory)
    (d : RepresentationExtraPreparation.Data n)
    (h : RepresentationPreparedFields.Agrees d
      (RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog history))
    (hp hq hr hi) : ofStored I d hp hq hr hi =
      RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog history := by
  have hc : (⟨fun p : Fin 4 × Fin (width n) =>
      (d.residues.primes.stored.coordinates p.1)[p.2.val], hi⟩ : TopCoordinates n (width n)) =
      (RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog history).coordinates := by
    apply coordinates_ext
    exact funext (fun p => h.coordinates p.1 p.2)
  unfold ofStored
  change _ = ({
    input := I
    signs := _
    leaves := _
    lowModuli := _
    firstResidues := _
    p0 := _
    p0_positive := _
    q := _
    q_positive := _
    rho0 := _
    capacity := compressionDictionaryCapacity n
    coordinates := _
    topOrder := _ } : RepresentationScheduleData n (width n))
  congr 1
  · exact h.signs
  · exact h.leaves
  · exact funext h.low
  · exact funext h.first
  · exact h.p0
  · exact proof_irrel_heq _ _
  · exact h.q
  · exact proof_irrel_heq _ _
  · exact (Fin.heq_ext_iff h.p0).2 h.rho0
  · exact h.order

theorem fromSuccess_eq (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    fromSuccess I hn hlog s d h =
      RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog
        (((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s) :=
  ofStored_eq I hn hlog _ d (RepresentationPreparedFields.agrees I hn hlog s d h) _ _ _ _

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (run I hn hlog s).2 ≤ (RepresentationExtraPreparation.run I hn hlog s).2 + 16 := by
  unfold run
  dsimp only
  split <;> dsimp only <;> omega

theorem schedule_run_congr (A B : RepresentationScheduleData n g) (h : A = B)
    (F : IndexedMask n) (hA : F.semantic = A.signs) (hB : F.semantic = B.signs)
    (capacity : ℕ) (blocks : List (StoredSeparatorCheck.Block n g)) (budget : ℕ) :
    BudgetedSchedule.run A F hA capacity blocks A.target budget =
      BudgetedSchedule.run B F hB capacity blocks B.target budget := by
  subst B
  rfl

end LowSpaceSubsetSum.RepresentationSchedulePreparation

end

end OAI
