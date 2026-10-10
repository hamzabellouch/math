import OAI.NumberTheory.Jacobsthal.Paths.ReferencePrefixRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceWeightedRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def weightedValue (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (F : List ℕ → ℝ) : ℝ :=
  ∑ ps ∈ referencePrefixes w P i r,signedWeight ps*F ps

theorem weighted_reference_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (F : List ℕ → ℝ) :
    weightedValue w P i r F=F []-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps*F ps else 0)
  have he : weightedValue w P i r F =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps*F ps else 0 := by
    rw [weightedValue,referencePrefixes,Finset.sum_filter]
  have hnil : (if admitted w i r [] then signedWeight []*F [] else 0)=F [] := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps)*F (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,weightedValue,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferenceWeightedRecurrence

end

section

namespace NumberTheoryLean.ReferenceForestTelescoping

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffixPrimes_nil (P : Finset ℕ) : suffixPrimes P []=P := by simp [suffixPrimes]

theorem suffixPrimes_cons (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    suffixPrimes P (p::ps)=suffixPrimes (P.filter (fun q => q<p)) ps := by
  ext q
  simp [suffixPrimes,and_assoc,and_left_comm,and_comm]

noncomputable def forestSum (w : ℝ) (P : Finset ℕ) (z : Node) (G : Finset ℕ → Node → ℝ) : ℝ :=
  weightedValue w P z.side z.gap (fun ps => G (suffixPrimes P ps) (terminal w z ps))

theorem forestSum_recurrence (w : ℝ) (P : Finset ℕ) (z : Node) (G : Finset ℕ → Node → ℝ) :
    forestSum w P z G=G P z-
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) G else 0 := by
  have h := weighted_reference_recurrence w P z.side z.gap (fun ps => G (suffixPrimes P ps) (terminal w z ps))
  simpa only [forestSum,suffixPrimes_nil,terminal_nil,suffixPrimes_cons,terminal_cons,step] using h

noncomputable def recurrenceResidual (w : ℝ) (G : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) : ℝ :=
  G P z+∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
    (p:ℝ)⁻¹*G (P.filter (fun q => q<p)) (step w z p) else 0

theorem actual_forest_telescoping (w : ℝ) (G : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) :
    forestSum w P z (recurrenceResidual w G)=G P z := by
  revert z
  refine Finset.strongInductionOn P ?_
  intro P ih z
  rw [forestSum_recurrence]
  have hs : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) (recurrenceResidual w G) else 0)=
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*G (P.filter (fun q => q<p)) (step w z p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hsmall : P.filter (fun q => q<p) ⊂ P :=
      Finset.filter_ssubset.mpr ⟨p,hp,lt_irrefl p⟩
    rw [ih _ hsmall]
  rw [hs,recurrenceResidual]
  ring

end NumberTheoryLean.ReferenceForestTelescoping

end

section

namespace NumberTheoryLean.ReferenceCutoffRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ReferenceWeightedRecurrence ReferenceForestTelescoping
open ErdosPrimeInputs.HarmonicPrimeMeasure

def Above (P Q : Finset ℕ) : Prop := ∀ p ∈ P,∀ q ∈ Q,q<p

theorem above_disjoint {P Q : Finset ℕ} (h : Above P Q) : Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact lt_irrefl p (h p hp p hq)

theorem union_filter_at_high {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ P) :
    (P∪Q).filter (fun q => q<p)=(P.filter (fun q => q<p))∪Q := by
  rw [Finset.filter_union,Finset.filter_eq_self.mpr (h p hp)]

theorem union_filter_at_low {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ Q) :
    (P∪Q).filter (fun q => q<p)=Q.filter (fun q => q<p) := by
  ext q
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hq,hqp⟩
    rcases hq with hq | hq
    · exact False.elim (lt_asymm hqp (h q hq p hp))
    · exact ⟨hq,hqp⟩
  · rintro ⟨hq,hqp⟩
    exact ⟨Or.inr hq,hqp⟩

theorem cutoff_polynomial_recurrence (w : ℝ) {P Q : Finset ℕ} (h : Above P Q) (i : Side) (r : ℝ) :
    referencePolynomial w (P∪Q) i r=referencePolynomial w Q i r-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
  have hfull := reference_polynomial_recurrence w (P∪Q) i r
  have hlow := reference_polynomial_recurrence w Q i r
  rw [Finset.sum_union (above_disjoint h)] at hfull
  have hh : (∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hl : (∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (Q.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hh,hl] at hfull
  linarith

noncomputable def cutoffInsertion (w : ℝ) (Q : Finset ℕ) (B : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) : ℝ :=
  referencePolynomial w Q z.side z.gap-B P z-
    ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*B (P.filter (fun q => q<p)) (step w z p) else 0

theorem difference_residual (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    recurrenceResidual w (fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y) P z=
      cutoffInsertion w Q B P z := by
  have hrec := cutoff_polynomial_recurrence w h z.side z.gap
  have hsum : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*(referencePolynomial w ((P.filter (fun q => q<p))∪Q) (step w z p).side (step w z p).gap-
        B (P.filter (fun q => q<p)) (step w z p)) else 0)=
    (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) z.side.flip (z.gap-primeExponent w p) else 0)-
    ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*B (P.filter (fun q => q<p)) (step w z p) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    split_ifs <;> simp [step,mul_sub]
  unfold recurrenceResidual cutoffInsertion
  dsimp only
  rw [hsum]
  linarith

theorem finite_cutoff_decomposition (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    referencePolynomial w (P∪Q) z.side z.gap-B P z=
      forestSum w P z (cutoffInsertion w Q B) := by
  let G : Finset ℕ → Node → ℝ := fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y
  have ht := actual_forest_telescoping w G P z
  change G P z=_
  rw [← ht]
  unfold forestSum weightedValue
  apply Finset.sum_congr rfl
  intro ps _hp
  have hsub : Above (suffixPrimes P ps) Q := by
    intro p hp q hq
    exact h p (Finset.mem_filter.mp hp).1 q hq
  dsimp only
  rw [show recurrenceResidual w G (suffixPrimes P ps) (terminal w z ps)=
      cutoffInsertion w Q B (suffixPrimes P ps) (terminal w z ps) from difference_residual w hsub B _]

end NumberTheoryLean.ReferenceCutoffRecurrence

end

end Erdos970

end OAI
