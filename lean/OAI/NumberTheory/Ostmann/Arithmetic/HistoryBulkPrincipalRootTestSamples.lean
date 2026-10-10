import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalRootTestBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalRootTest
open Construction ResidueHaar HistoryBulkSelectedIntegralReplacement HistoryBulkResidueRootAverage
open HistoryBulkResidueNormSum HistoryBulkSpectatorProduct HistoryFrequencyResidues HistoryCRTIntegration
open HistoryBulkSpectatorReferenceRaw HistoryBulkProducts CanonicalHistoryLeafBulk

theorem sourceBulkUnits_map (M D : ℕ) (hD : D∣M) (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hc : Nat.Coprime (bulkProduct (assignedSlots sources
      (Template.current (Template.initial m k) l) x)) M)
    (u : Fin (2^l)×Fin m) :
    ZMod.unitsMap hD (sourceBulkUnits M sources m k l x u)=sourceBulkUnits D sources m k l x u := by
  apply Units.ext
  change (ZMod.cast (sourceBulkUnits M sources m k l x u:ZMod M):ZMod D)=_
  rw [sourceBulkUnits_coe M sources m k l x hc u,ZMod.cast_natCast hD,
    sourceBulkUnits_coe D sources m k l x (hc.of_dvd_right hD) u]

variable (d : Decomposition) {l m k₀ : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    [NeZero outside.prod] [NeZero (pairedFrequencyProduct h k)]
    (sources : SourceFamily)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
    (hc : Nat.Coprime (bulkProduct (assignedSlots sources
      (Template.current (Template.initial m k₀) l) x))
      (outside.prod*(pairedFrequencyProduct h k)^(K+2)))

include hc

theorem independent_unit_source_eq_product :
    rootTest true false d h k hs ks hp hV σ K
      (sourceBulkUnits (outside.prod*(pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)=
      average (fun z : UnitPair outside.prod=>
        unitTest h k hs ks hp hV σ (residueTransform d) z
          (sourceBulkUnits outside.prod sources m k₀ l x))*
      average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
        independentRTest K h k σ ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (sourceBulkUnits ((pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)) := by
  rw [independent_unit_eq_product]
  simp only [sourceBulkUnits_map _ _ _ sources m k₀ l x hc]

theorem independent_mixed_source_eq_product :
    rootTest true true d h k hs ks hp hV σ K
      (sourceBulkUnits (outside.prod*(pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)=
      average (fun z : MixedPair outside.prod=>
        mixedTest h k hs ks hp hV σ (residueTransform d) z
          (sourceBulkUnits outside.prod sources m k₀ l x))*
      average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
        independentRTest K h k σ ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (sourceBulkUnits ((pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)) := by
  rw [independent_mixed_eq_product]
  simp only [sourceBulkUnits_map _ _ _ sources m k₀ l x hc]

theorem canonical_unit_source_eq_product :
    rootTest false false d h k hs ks hp hV σ K
      (sourceBulkUnits (outside.prod*(pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)=
      average (fun z : UnitPair outside.prod=>
        unitTest h k hs ks hp hV σ (residueTransform d) z
          (sourceBulkUnits outside.prod sources m k₀ l x))*
      average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
        canonicalRTest K h k ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (sourceBulkUnits ((pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)) := by
  rw [canonical_unit_eq_product]
  simp only [sourceBulkUnits_map _ _ _ sources m k₀ l x hc]

theorem canonical_mixed_source_eq_product :
    rootTest false true d h k hs ks hp hV σ K
      (sourceBulkUnits (outside.prod*(pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)=
      average (fun z : MixedPair outside.prod=>
        mixedTest h k hs ks hp hV σ (residueTransform d) z
          (sourceBulkUnits outside.prod sources m k₀ l x))*
      average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
        canonicalRTest K h k ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (sourceBulkUnits ((pairedFrequencyProduct h k)^(K+2)) sources m k₀ l x)) := by
  rw [canonical_mixed_eq_product]
  simp only [sourceBulkUnits_map _ _ _ sources m k₀ l x hc]

end Ostmann.Arithmetic.HistoryBulkPrincipalRootTest

end

end OAI
