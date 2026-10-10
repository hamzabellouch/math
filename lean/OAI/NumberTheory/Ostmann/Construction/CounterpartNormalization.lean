import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.RemainingRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def sourceNormalization (C : InitialSourceChoice d Bs BD Bz k L E) : ℕ→ℝ :=
  initialSourceValue (Conclusion.bulkSize k L/2) k (harmonicPrimeMass (bulkPrimeBand L E))⁻¹
    (fun i => (logCellMass (C.cells.top i) E)⁻¹)
    (fun j i => (logCellMass (C.cells.comp j i) E)⁻¹)

def sourceCutoff (C : InitialSourceChoice d Bs BD Bz k L E) (origin p : ℕ) : ℝ :=
  initialSourceValue (Conclusion.bulkSize k L/2) k 1
    (fun i => Ostmann.smoothPartition (Real.log p-C.cells.top i))
    (fun j i => Ostmann.smoothPartition (Real.log p-C.cells.comp j i)) origin

theorem source_mass_normalization (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ℕ) (p : (C.sources origin).Sample) :
    (C.sources origin).law.mass p=C.sourceNormalization origin*C.sourceCutoff origin p/(p:ℕ) := by
  revert p
  by_cases hb : origin<2*(Conclusion.bulkSize k L/2)
  · have hS : C.sources origin=C.bulk := by
      simp only [sources,NominalCenterArray.sources,initialSourceFamily,initialSourceValue,hb,ite_true]
    rw [hS]
    intro p
    rw [show C.bulk.law.mass p=1/((p:ℕ)*harmonicPrimeMass (bulkPrimeBand L E)) from
      harmonicPrimeSource_mass _ _ C.bulkPositive p]
    simp only [sourceNormalization,sourceCutoff,initialSourceValue,hb,ite_true]
    ring
  · by_cases ht : origin<2*(Conclusion.bulkSize k L/2)+6
    · let i : Fin 3 := ⟨(origin-2*(Conclusion.bulkSize k L/2))%3,Nat.mod_lt _ (by decide)⟩
      have hS : C.sources origin=C.cells.topSource E C.deleted_card i := by
        simp only [sources,NominalCenterArray.sources,initialSourceFamily,initialSourceValue,hb,ht,ite_false,ite_true]
        rfl
      rw [hS]
      intro p
      rw [show (C.cells.topSource E C.deleted_card i).law.mass p=
          Ostmann.smoothPartition (Real.log (p:ℕ)-C.cells.top i)/((p:ℕ)*logCellMass (C.cells.top i) E) from
        balancedCellSource_mass d _ _ E C.deleted_card p]
      simp only [sourceNormalization,sourceCutoff,initialSourceValue,hb,ht,ite_false,ite_true]
      dsimp only [i]
      ring
    · by_cases hc : (origin-(2*(Conclusion.bulkSize k L/2)+6))/4<k
      · let j : Fin k := ⟨(origin-(2*(Conclusion.bulkSize k L/2)+6))/4,hc⟩
        let i : Fin 2 := ⟨(origin-(2*(Conclusion.bulkSize k L/2)+6))%2,Nat.mod_lt _ (by decide)⟩
        have hS : C.sources origin=C.cells.compSource E C.deleted_card j i := by
          simp only [sources,NominalCenterArray.sources,initialSourceFamily,initialSourceValue,hb,ht,hc,ite_false,dite_true]
          rfl
        rw [hS]
        intro p
        rw [show (C.cells.compSource E C.deleted_card j i).law.mass p=
            Ostmann.smoothPartition (Real.log (p:ℕ)-C.cells.comp j i)/((p:ℕ)*logCellMass (C.cells.comp j i) E) from
          balancedCellSource_mass d _ _ E C.deleted_card p]
        simp only [sourceNormalization,sourceCutoff,initialSourceValue,hb,ht,hc,ite_false,dite_true]
        dsimp only [i,j]
        ring
      · have hS : C.sources origin=C.bulk := by
          simp only [sources,NominalCenterArray.sources,initialSourceFamily,initialSourceValue,hb,ht,hc,ite_false,dite_false]
        rw [hS]
        intro p
        rw [show C.bulk.law.mass p=1/((p:ℕ)*harmonicPrimeMass (bulkPrimeBand L E)) from
          harmonicPrimeSource_mass _ _ C.bulkPositive p]
        simp only [sourceNormalization,sourceCutoff,initialSourceValue,hb,ht,hc,ite_false,dite_false]
        ring

theorem sourceMass_normalization (C : InitialSourceChoice d Bs BD Bz k L E) (q : SmallSlot) :
    sourceMass C.sources q=
      if q.value∈(C.sources q.origin).candidates then
        C.sourceNormalization q.origin*C.sourceCutoff q.origin q.value/q.value else 0 := by
  unfold sourceMass
  split_ifs with hq
  · exact C.source_mass_normalization q.origin ⟨q.value,hq⟩
  · rfl

def remainingNormalization (C : InitialSourceChoice d Bs BD Bz k L E) (T : List SourceSlot) : ℝ :=
  (logCellMass C.giantCenter ∅)⁻¹*(T.map (fun q => C.sourceNormalization q.origin)).prod

def remainingCutoff (C : InitialSourceChoice d Bs BD Bz k L E) (T : List SourceSlot)
    (y : RemainingSample C.sources T C.giant) : ℝ :=
  Ostmann.smoothPartition (Real.log (y.1.val:ℝ)-C.giantCenter)*
    ∏i:Fin T.length,C.sourceCutoff T[i].origin (y.2 i)

theorem remaining_mass_normalization (C : InitialSourceChoice d Bs BD Bz k L E)
    (T : List SourceSlot) (y : RemainingSample C.sources T C.giant) :
    (remainingPrior C.sources T C.giant).mass y=
      C.remainingNormalization T/(remainingProduct C.sources T C.giant y:ℝ)*C.remainingCutoff T y := by
  change C.giant.law.mass y.1*(∏i:Fin T.length,(C.sources T[i].origin).law.mass (y.2 i))=_
  rw [show C.giant.law.mass y.1=Ostmann.smoothPartition (Real.log (y.1.val:ℝ)-C.giantCenter)/
      ((y.1.val:ℝ)*logCellMass C.giantCenter ∅) from logCellPrior_mass _ _ C.giantPositive y.1]
  simp_rw [source_mass_normalization]
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  have hn : (T.map (fun q => C.sourceNormalization q.origin)).prod=
      ∏i:Fin T.length,C.sourceNormalization T[i].origin := by
    rw [←List.ofFn_getElem_eq_map,List.prod_ofFn]
    rfl
  have hv : ((assignedSlots C.sources T y.2).map SmallSlot.value).prod=
      ∏i:Fin T.length,(y.2 i).val := by
    simp only [assignedSlots,Template.sample,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  simp only [remainingNormalization,remainingCutoff,remainingProduct,halfProduct,Nat.cast_mul,hn,hv,Nat.cast_prod]
  ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
