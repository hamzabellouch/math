import OAI.Combinatorics.ContingencyTables.Transport.TabulationMeasureBounds
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalPointBounds
import OAI.Combinatorics.ContingencyTables.Machines.ScheduledCountInput

namespace OAI

/-! # Uniform bounds for the executed nested trial-vector loops -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma terminalColumnMeasure_le (z : TerminalColumnInput) (M : ℕ)
    (hz : weight z.1 ≤ M) (hT : weight z.2 ≤ M)
    (hN : gridStateCount (profileEnumerationData (matrixData z.1)) ≤ M)
    (hv : ∀ v∈profileBoxViews (matrixData z.1),weight v ≤ M)
    (he : ∀ v∈profileBoxViews (matrixData z.1),matrixEntryMeasure (z.1,(v,v)) ≤ M) :
    terminalColumnMeasure z ≤ (M+1)*(8*M+8) := by
  let vs := profileBoxViews (matrixData z.1)
  have hzz : weight z=1+weight z.1+weight z.2 := by
    rcases z with ⟨z,T⟩
    simp only [weight_prod]
  have hlen : vs.length ≤ M := (profileBoxViews_length _).le.trans hN
  have hvs : weight vs ≤ M*(M+1)+1 :=
    (list_weight_bound vs M hv).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hentry (v : List ℕ×List ℕ) (hv' : v∈vs) :
      terminalColumnEntryMeasure (z,v) ≤ 7*M+4 := by
    have hw := hv v hv'
    have hm := he v hv'
    change matrixEntryMeasure (z.1,(v,v))+weight (z.1,(v,z.2))+weight (z,v) ≤ _
    simp only [weight_prod]
    rw [hzz]
    nlinarith
  have hs := MeasuredMap.listMeasure_le terminalColumnEntryMeasure z vs (7*M+4) hentry
  have hp : weight (z,vs) ≤ 3+2*M+M*(M+1) := by
    simp only [weight_prod]
    rw [hzz]
    omega
  have hm : terminalColumnMeasure z ≤ M+(3+2*M+M*(M+1))+M*(7*M+4) := by
    have hb := Nat.mul_le_mul_right (7*M+4) hlen
    change gridStateCount (profileEnumerationData (matrixData z.1))+
      MeasuredMap.listMeasure terminalColumnEntryMeasure (z,vs) ≤ _
    omega
  exact hm.trans (by nlinarith)

lemma unit_terminalColumnMeasure_le (z : TerminalColumnInput) :
    UnitCountPrograms.terminalColumnMeasure z ≤ terminalColumnMeasure z := by
  unfold UnitCountPrograms.terminalColumnMeasure terminalColumnMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro v _
  change weight (z.1,(v,z.2))+weight (z,v) ≤
    (matrixEntryMeasure (terminalSourceInput (z.1,(v,z.2)))+weight (z.1,(v,z.2)))+weight (z,v)
  omega

lemma unit_outerVectorMeasure_le (z : OuterVectorInput) :
    UnitCountPrograms.outerVectorMeasure z ≤ outerVectorMeasure z := by
  apply Nat.add_le_add_right
  unfold UnitCountPrograms.trialVectorMeasure trialVectorMeasure
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro o _
  change UnitCountPrograms.trialCountMeasure (optionalTrialInput (z.1.1,o))+weight (z.1.1,o) ≤
    trialCountMeasure (optionalTrialInput (z.1.1,o))+weight (z.1.1,o)
  apply Nat.add_le_add_right
  unfold UnitCountPrograms.trialCountMeasure trialCountMeasure
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · unfold UnitCountPrograms.walkCountMeasure walkCountMeasure
    exact Nat.add_le_add_right (Nat.add_le_add_left (unitMatrixMeasure_le _) _) _
  · exact unit_terminalColumnMeasure_le _

noncomputable def vectorMeasurePolynomial : Polynomial ℕ :=
  let mat := (X+1)^2*(4*X+7)
  let terminal := (X+1)*(8*X+8)
  X*(mat+terminal+6*X+2)+X*(X+1)+5*X+2

theorem outerVectorMeasure_bound (z : OuterVectorInput) (M : ℕ)
    (hz : weight z ≤ M) (hsteps : z.1.1.2.1 ≤ M)
    (hO : gridStateCount (originalEnumerationData z.1.2) ≤ M)
    (hN : gridStateCount (profileEnumerationData (matrixData z.1.1.1)) ≤ M)
    (hv : ∀ v∈profileBoxViews (matrixData z.1.1.1),weight v ≤ M)
    (ho : ∀ o∈originalCandidates z.1.2,weight o ≤ M ∧ weight (o.getD []) ≤ M)
    (he : ∀ u∈profileBoxViews (matrixData z.1.1.1),
      ∀ v∈profileBoxViews (matrixData z.1.1.1),matrixEntryMeasure (z.1.1.1,(u,v)) ≤ M) :
    outerVectorMeasure z ≤ vectorMeasurePolynomial.eval M := by
  let mat := (M+1)^2*(4*M+7)
  let terminal := (M+1)*(8*M+8)
  let B := mat+terminal+6*M+2
  let os := originalCandidates z.1.2
  have hw : weight z.1.1 ≤ M := (weight_fst _).trans ((weight_fst _).trans hz)
  have hm : weight z.1.1.1 ≤ M := (weight_fst _).trans hw
  have hr : weight z.1.2 ≤ M := (weight_snd _).trans ((weight_fst _).trans hz)
  have hmat : profileMatrixMeasure z.1.1.1 ≤ mat := by
    have h := profileMatrixMeasure_le z.1.1.1 M M hm hv he
    exact h.trans (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 2)
      (by omega))
  have hlen : os.length ≤ M := (originalCandidates_length _).le.trans hO
  have hos : weight os ≤ M*(M+1)+1 :=
    (list_weight_bound os M (fun o ho' => (ho o ho').1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hop (o : Option MatrixCode) (ho' : o∈os) : optionalTrialMeasure (z.1.1,o) ≤ B := by
    have hT := (ho o ho').2
    have how := (ho o ho').1
    have ht : terminalColumnMeasure (z.1.1.1,o.getD []) ≤ terminal :=
      terminalColumnMeasure_le _ M hm hT hN hv (fun v hv' => he v hv' v hv')
    change (z.1.1.2.1+profileMatrixMeasure z.1.1.1+weight z.1.1)+
      terminalColumnMeasure (z.1.1.1,o.getD [])+weight (z.1.1,o.getD [])+weight (z.1.1,o) ≤ B
    simp only [weight_prod]
    unfold B
    omega
  have hs := MeasuredMap.listMeasure_le optionalTrialMeasure z.1.1 os B hop
  have hmul := Nat.mul_le_mul_right B hlen
  have hpair : weight (z.1.1,os) ≤ 2+M+M*(M+1) := by
    simp only [weight_prod]
    omega
  change originalEnumerationMeasure z.1.2+
    MeasuredMap.listMeasure optionalTrialMeasure (z.1.1,os)+weight z.1+weight z ≤ _
  have hz1 : weight z.1 ≤ M := (weight_fst _).trans hz
  have horig : originalEnumerationMeasure z.1.2 ≤ 2*M := by
    unfold originalEnumerationMeasure
    omega
  simp only [vectorMeasurePolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  change _ ≤ M*B+M*(M+1)+5*M+2
  omega

end ContingencyTables.ProfilePrograms

end OAI
