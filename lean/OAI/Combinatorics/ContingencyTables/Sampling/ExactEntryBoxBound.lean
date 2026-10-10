import OAI.Combinatorics.ContingencyTables.Transport.ResidualBoxScale
import OAI.Combinatorics.ContingencyTables.Transport.TabulationPreparationBounds

namespace OAI

/-! # The actual transition-cache boxes in the exact sampler -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] unaryMarkers parameterProposalWidth scheduledCacheParameters
  residualParameters canonicalCountInput

private lemma proposalBox_eq (z : SamplingParameters) (u v : List ℕ×List ℕ) :
    gridStateCount ((scheduledMatrixParameters z,(u,v)).1.2,2)=2^(parameterProposalWidth z) := by
  have hm : (scheduledMatrixParameters z,(u,v)).1.2=unaryMarkers (parameterProposalWidth z) := by
    unfold scheduledMatrixParameters
    rfl
  rw [hm,gridStateCount_eq,unaryMarkers_length]

theorem exact_entry_box_bound : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    ∀ u∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn c)),
    ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn c)),
    matrixEntryBox (scheduledMatrixParameters (exactSamplingParameters (List.ofFn r,List.ofFn c)),(u,v)) ≤
      p.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c := by
  obtain ⟨a,ha⟩ := exact_count_input_measure_polynomial
  obtain ⟨b,hb⟩ := tabulation_preparation_polynomial
  obtain ⟨p,hp⟩ := matrixEntryBox_bound
  let A := b.comp a
  refine ⟨p.comp A+A+4,?_⟩
  intro m n r c htotal u hu v hv
  let z := exactSamplingParameters (List.ofFn r,List.ofFn c)
  let e : MatrixEntryInput := (scheduledMatrixParameters z,(u,v))
  let V := candidateData (initialCheck (List.ofFn r,List.ofFn c),u)
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  let S := Algorithms.samplingSize n r 0
  let E := exactBoxScale r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hbits : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have h23 : dim^2 ≤ dim^3 := Nat.pow_le_pow_right hd (by decide)
  have he : 1 ≤ E := exactBoxScale_pos r c
  have hdim : parameterDimension z=dim := by
    change marginDimension (List.ofFn r,List.ofFn c)=dim
    exact marginDimension_ofFn r c
  have hVrow : V.1.2.1=List.ofFn r := rfl
  have hVcol : V.1.2.2=List.ofFn c := rfl
  have hres : entryResidualParameters e=residualParameters ((V,dim^12),(dim,parameterAccuracy z)) := by
    unfold entryResidualParameters
    dsimp only [e,entryCacheParameters,sourceData,scheduledMatrixParameters,scheduledCacheParameters,matrixData]
    unfold scheduledCacheParameters
    dsimp only
    rw [show z.1=(List.ofFn r,List.ofFn c) from rfl,marginPadding_ofFn,hdim]
  have hnorm := normalized_profile_completion_count r c V hVrow hVcol (parameterAccuracy z)
  have hdense := normalized_profile_dense_grid r c V hVrow hVcol (parameterAccuracy z)
  have horig : gridStateCount (completionEnumerationData (entryResidualParameters e).1) ≤ E := by
    rw [hres]
    unfold residualParameters
    have hh := arbitrary_profile_completion_count r c V hVrow hVcol
    apply hh.trans
    apply Nat.pow_le_pow_right (by decide)
    have hmul : dim^2*bits ≤ dim^3*bits := Nat.mul_le_mul_right bits h23
    change 4*(dim^2*bits) ≤ 40*(dim^3*bits)
    omega
  have hprop : gridStateCount (e.1.2,2) ≤ E := by
    rw [proposalBox_eq z u v,parameterProposalWidth,hdim]
    apply Nat.pow_le_pow_right (by decide)
    have hc : Nat.clog 2 (32*dim^2) ≤ 32*dim^2 :=
      Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    have hmul : dim^3 ≤ dim^3*bits := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (dim^3) hbits
    exact hc.trans (by change 32*dim^2 ≤ 40*(dim^3*bits); nlinarith)
  have hprepare := hb z
  have hnum : parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ A.eval S :=
    hprepare.2.1.trans (by simp only [A,eval_comp]; exact polynomial_eval_monotone b (ha m n r c htotal))
  have hw : weight e ≤ A.eval S := (hprepare.2.2.2.2 u hu v hv).trans (by
    simp only [A,eval_comp]; exact polynomial_eval_monotone b (ha m n r c htotal))
  have hpoly : p.eval (weight e) ≤ p.eval (A.eval S) := polynomial_eval_monotone p hw
  have hbound := hp e
  dsimp only at hbound
  have hn : gridStateCount (completionEnumerationData (canonicalCountInput (entryResidualParameters e)).1.1) ≤ E := by
    rw [hres]
    exact hnorm
  have hg : (4*(canonicalCountInput (entryResidualParameters e)).1.2.1^8)^
      tabulationDimension (canonicalCountInput (entryResidualParameters e)).1 ≤ E := by
    rw [hres]
    exact hdense
  change matrixEntryBox e ≤ _
  have hrs : (entryResidualParameters e).2=(parameterDimension z,parameterAccuracy z) := by
    rw [hres]
    unfold residualParameters
    rw [hdim]
  have hcache : (entryCacheParameters e).2=parameterCompletionWidth z := by
    unfold e entryCacheParameters scheduledMatrixParameters
    unfold scheduledCacheParameters
    rfl
  have hnum' : (entryResidualParameters e).2.1+(entryResidualParameters e).2.2+
      (entryCacheParameters e).2 ≤ A.eval S := by
    rw [hrs,hcache]
    exact hnum
  have hfirst : matrixEntryBox e ≤ 4*E+A.eval S+p.eval (A.eval S) := by
    omega
  apply hfirst.trans
  have hA : A.eval S ≤ A.eval S*E := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A.eval S) he
  have hpA : p.eval (A.eval S) ≤ p.eval (A.eval S)*E := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (p.eval (A.eval S)) he
  simp only [eval_add,eval_comp,eval_ofNat]
  nlinarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
