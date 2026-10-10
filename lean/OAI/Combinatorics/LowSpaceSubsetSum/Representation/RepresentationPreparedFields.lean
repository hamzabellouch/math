import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFromFamilies

namespace OAI

/-! # All stored fields belong to one accepted representation history -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPreparedFields

variable {n : ℕ}

structure Agrees (d : RepresentationExtraPreparation.Data n)
    (S : RepresentationScheduleData n (StoredTopCoordinates.width n)) : Prop where
  signs : d.residues.primes.stored.stored.layout.signs.semantic = S.signs
  leaves : d.residues.primes.stored.leaves = S.leaves
  low : ∀ j : Fin 2, d.residues.primes.moduli[j.val + 1] = S.lowModuli j
  p0 : d.residues.primes.moduli[0] = S.p0
  first : ∀ j : Fin 2,
    (if j = 0 then (d.residues.residues[1] : ℤ) else d.residues.residues[2]) = S.firstResidues j
  rho0 : d.residues.residues[0] = S.rho0.val
  q : d.q = S.q
  coordinates : ∀ (a : Fin 4) (k : Fin (StoredTopCoordinates.width n)),
    (d.residues.primes.stored.coordinates a)[k.val] = S.coordinates.index (a, k)
  order : (StoredOrderedMixers.lists d.residues.primes.stored.stored.layout)[0] = S.topOrder

theorem agrees (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (data : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some data) :
    Agrees data (RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog
      (((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s)) := by
  let R := (canonicalRepresentationData I).zeroSetup
  obtain ⟨extra, he, hr, hq⟩ := RepresentationExtraPreparation.source I hn hlog s data h
  have hie := (R.extraHistoryExecution (by omega)).ideal_eq_of_some s extra
    (((R.extraHistoryExecution (by omega)).value_eq s).trans he)
  obtain ⟨trial, ht, hp, hres⟩ := RepresentationResiduePreparation.source I hn hlog s.1 data.residues hr
  have hit := R.trialHistoryExecution.ideal_eq_of_some s.1 trial
    ((R.trialHistoryExecution.value_eq s.1).trans ht)
  obtain ⟨prime, hprime, hs, _, hm⟩ :=
    RepresentationPrimePreparation.source I hn hlog s.1.1 data.residues.primes hp
  have hip := R.primeHistoryExecution.ideal_eq_of_some s.1.1 prime
    ((R.primeHistoryExecution.value_eq s.1.1).trans hprime)
  obtain ⟨part, hpart, hsign, hv, _, _, hl, hc⟩ :=
    RepresentationStoredPreparation.source I s.1.1.1 data.residues.primes.stored hs hn hlog
  have his := R.partitionHistoryExecution.ideal_eq_of_some s.1.1.1 part
    ((R.partitionHistoryExecution.value_eq s.1.1.1).trans hpart)
  rw [← his] at hsign hv hl hc
  rw [← hip] at hm
  rw [← hit] at hres
  rw [← hie] at hq
  have hpref := RepresentationStoredPreparation.prefix_result I s.1.1.1 data.residues.primes.stored hs
  have hL := (RepresentationPrefixArrays.components (canonicalRepresentationData I)
    s.1.1.1 data.residues.primes.stored.stored hpref).1
  have ho := StoredOrderedMixers.lists_source (canonicalRepresentationData I) s.1.1.1.1.1
    data.residues.primes.stored.stored.layout hL
    (R.partitionHistoryCoupling.ideal s.1.1.1).1.1.1 hv
    (R.partitionHistoryCoupling.ideal s.1.1.1).1.1.2 0
  constructor
  · exact hsign
  · exact funext (fun side => funext (hl side))
  · intro j
    exact hm j.succ
  · exact hm 0
  · intro j
    rw [hres]
    rfl
  · rw [hres]
    rfl
  · exact hq
  · exact hc
  · exact ho

end LowSpaceSubsetSum.RepresentationPreparedFields

end

end OAI
