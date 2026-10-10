import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCapacity
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary HeckeDetectorRawFiber ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma oriented_moment_nonzero_base (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O, idealCoeff χ I=if reverse then
      conj (idealCoeff ((momentData η).character (momentElement u)) I)
      else idealCoeff ((momentData η).character (momentElement u)) I)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff η I≠0 := by
  intro he
  have hh:=hc I
  rw [momentData_product_raw,idealCoeff_product,he,zero_mul] at hh
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_zero] at hh
  · exact hI hh
  · exact hI hh

lemma fiber_nonzero_initial {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0) : idealCoeff η I≠0 := by
  apply oriented_moment_nonzero_base η (F.family u F.label) u F.reverse ?_ I hI
  simpa only [hdata,momentElement] using F.row_coeff u hu

lemma ideal_nonzero_forcing_coprime (η : Character) (I P : Ideal O)
    (hI : idealCoeff η I≠0) (hP : P∣I) : IsCoprime η.modulus P := by
  have hI0 : I≠0 := by intro h; apply hI; rw [h,map_zero]
  have he : elementCoeff η (idealGenerator I)≠0 := by
    rw [←idealCoeff_span η (idealGenerator_ne_zero I hI0),span_idealGenerator]
    exact hI
  exact CenteredMomentChildRows.old_coefficient_prime_coprime η (idealGenerator I) he P
    (by rwa [span_idealGenerator])

theorem fiber_internal_forcing {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I Q P : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0)
    (hP : P∣I) (hQP : IsCoprime Q P) : IsCoprime (internalQ Q η) P :=
  internalQ_coprime Q P η hQP
    (ideal_nonzero_forcing_coprime η I P (fiber_nonzero_initial F η hdata u hu I hI) hP)

theorem fiber_initial_support_filter {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (s : Finset (Ideal O)) (weight : Ideal O→ℂ) :
    (∑I∈s,idealCoeff (F.family u F.label) I*weight I)=
      ∑I∈s.filter (fun I=>idealCoeff η I≠0),idealCoeff (F.family u F.label) I*weight I := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hIs hnot
  have hzero : idealCoeff (F.family u F.label) I=0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hIs,fiber_nonzero_initial F η hdata u hu I hn⟩)
  rw [hzero,zero_mul]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
