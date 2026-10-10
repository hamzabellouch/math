import OAI.Combinatorics.ContingencyTables.Counting.CompanionUniformPhaseWidth
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartScheduleSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicWordBound

namespace OAI

/-! # The computed common width covers every actual phase and marker -/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open RootedPhaseHistory GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (s : Settings A) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K) : Input :=
  CompanionRestartInitializer.data A s.C s.K s.H (CompanionTargetMixing.restartTime A s.H s.L)
    s.N s.n s.L epsilon z v

lemma fields_data (A : Instance (Fin m) (Fin n)) (s : Settings A)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon)=s.k)
    (hh : s.h=CountingPhaseSchedule.initialPrecision s.H) :
    fields (data A s epsilon z v)=
      [A.d,s.K,rationalHeight A s.C,0,Fintype.card (Labels A),A.W,s.H,
        CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L,s.k,s.h] := by
  have ho : oracleInput (data A s epsilon z v)=RootedOracleConfigProgram.data A s.C s.K 0
      (CountingPhaseParametersProgram.noise
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon))
      z v [] := rfl
  unfold fields rawFields
  rw [ho,RootedOracleConfigProgram.fields_data]
  change [A.d,s.K,rationalHeight A s.C,0]++
    [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]++
      [CountingPhaseParametersProgram.precision
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon),
        CountingPhaseScalarProgram.initialPrecision.eval
          [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]]=_
  rw [hk,CountingPhaseScalarProgram.initialPrecision_value,←hh]
  rfl

theorem width_covers (A : Instance (Fin m) (Fin n)) (s : Settings A)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon)=s.k)
    (hh : s.h=CountingPhaseSchedule.initialPrecision s.H)
    (hxi : s.xi=1/(s.k:ℚ)) (hkpos : 0 < s.k) (hHpos : 0 < s.H)
    (hcap : CountingTerminalSchedule.capacityBits A ≤ s.L) :
    totalWidth A s ≤ width (data A s epsilon z v) ∧
      (∀ j,j ≤ s.H →
        PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (s.xi/2) j))+
          PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (s.xi/2) j)) ≤
            width (data A s epsilon z v)) ∧
      2*Fintype.card (Labels A) ≤ width (data A s epsilon z v) := by
  let M := measure (data A s epsilon z v)
  have hs : ∀ x,x ∈ [A.d,s.K,rationalHeight A s.C,0,Fintype.card (Labels A),A.W,s.H,
      CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L,s.k,s.h] → x ≤ M := by
    intro x hx
    have hmem : x ∈ fields (data A s epsilon z v) := by
      rw [fields_data A s epsilon z v hk hh]
      exact hx
    exact (List.le_sum_of_mem hmem).trans (Nat.le_succ _)
  have hd : A.d ≤ M := hs _ (by simp)
  have hK : s.K ≤ M := hs _ (by simp)
  have hheight : rationalHeight A s.C ≤ M := hs _ (by simp)
  have hp : Fintype.card (Labels A) ≤ M := hs _ (by simp)
  have hW : A.W ≤ M := hs _ (by simp)
  have hH : s.H ≤ M := hs _ (by simp)
  have ht : CompanionTargetMixing.restartTime A s.H s.L ≤ M := hs _ (by simp)
  have hN : s.N ≤ M := hs _ (by simp)
  have hn : s.n ≤ M := hs _ (by simp)
  have hL : s.L ≤ M := hs _ (by simp)
  have hkM : s.k ≤ M := hs _ (by simp)
  have hhM : s.h ≤ M := hs _ (by simp)
  have hr := CountingPublicWordBound.reciprocal_controls s.k M hkpos hkM
  have hx0 : 0 < s.xi := by rw [hxi]; exact hr.1
  have hxiM : 1/s.xi ≤ (M:ℚ) := by rw [hxi]; exact hr.2.1
  have hrepeats : CommonBasesFPRAS.repetitionCount s.xi ≤ 64*(M+1) := by
    rw [hxi]
    exact hr.2.2
  have hb := CountingWordsBound.bitCount_bound A s M hd hW hK hH hkM hn hN hhM hheight
    (hcap.trans hL) hp ht hx0 hxiM hrepeats
  have htotal : totalWidth A s ≤ RootedCountingWords.bitCount A s := by
    change totalWidth A s ≤ s.H*totalWidth A s
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (totalWidth A s) hHpos
  have hb' := htotal.trans hb
  dsimp only [M] at hb' hp
  simp only [width_value]
  refine ⟨hb'.trans (by omega),?_,?_⟩
  · intro j hj
    have hm := CountingMarkerBounds.padding_bound j M s.xi (hj.trans hH) hx0 hxiM
    dsimp only [M] at hm
    exact hm.trans (by omega)
  · omega

end
end ContingencyTables.CompanionUniformPhaseWidth

end OAI
