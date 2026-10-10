import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer
open InverseInitialConjugateEnergy
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)
    (P:Ideal O) : ℂ := slotCoefficient F.rowData (F.profile s) (U^(F.widths s)) (F.external s) P

omit [NeZero M] in
theorem fiberLists_prime (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(s:selected)(P:Ideal O)(hP:P∈fiberLists F selected s) : Prime P := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1

omit [NeZero M] in
theorem fiberLists_disjoint (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s)) :
    ((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hp:=livePrime_data M H (F.profile s) (lower s) (F.upper s) (U^(F.widths s))
    (Real.rpow_pos_of_pos hU _) (hV s s.property) P hP
  have hq:=livePrime_data M H (F.profile t) (lower t) (F.upper t) (U^(F.widths t))
    (Real.rpow_pos_of_pos hU _) (hV t t.property) P hQ
  rcases hsep s s.property t t.property (fun he=>hst (Subtype.ext he)) with h|h <;>
    linarith [hp.2.2.1,hp.2.2.2,hq.2.2.1,hq.2.2.2]

omit [NeZero M] in
theorem selectedSource_tuple (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(u:O) :
    selectedSource F selected W σ t bW u=
      ∑q:Tuple (fiberLists F selected),(∏s:selected,fiberCoefficient F s (q s).val)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,(q s).val) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  rw [sum_tuple_original (fiberLists F selected) (fun q=>
    (∏s:selected,fiberCoefficient F s (q s))*originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,q s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u)]
  unfold selectedSource
  apply Finset.sum_congr rfl
  intro q hq
  rw [tuple_coefficient]
  rfl

omit [NeZero M] in
theorem selectedSource_overlap (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(hU:0<U)
    (hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected))
    (u:O) :
    selectedSource F selected W σ t bW u=
      ∑J∈(Finset.univ:Finset selected).powerset,∑x:Assigned (fiberLists F selected) J,
        assignedTerm
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (fiberLists F selected) J x (fun s=>fiberCoefficient F s)
          (fixedBase F.rowData.η F.rowData.m F.rowData.f)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) (∑s∈J,F.widths s) u := by
  rw [selectedSource_tuple]
  exact original_selected_overlap _ (fiberLists F selected) (fiberLists_prime F selected)
    hdis (fun s=>fiberCoefficient F s) _ (fun _=>1) _ U F.r _
    (fun J=>∑s∈J,F.widths s) hU u

omit [NeZero M] in
theorem fiberAssigned_admissible (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s))
    (J:Finset selected)(x:Assigned (fiberLists F selected) J) :
    CanonicalQuadraticSieve.Admissible (assignedIdeal (fiberLists F selected) J x) := by
  have hdis:=fiberLists_disjoint F selected lower hU hV hsep
  have hp (s:↥J):Prime (x s).val:=fiberLists_prime F selected s.val _ (x s).property
  have hinj:Function.Injective (fun s:↥J=>(x s).val) := by
    intro s t he
    apply Subtype.ext
    by_contra hst
    exact Finset.disjoint_left.mp (hdis (Finset.mem_univ s.val) (Finset.mem_univ t.val) hst)
      (x s).property (by simpa only [he] using (x t).property)
  have hs (s:↥J):CanonicalQuadraticSieve.Supported (x s).val := by
    by_contra hn
    have hd:=livePrime_data M H (F.profile s.val) (lower s.val) (F.upper s.val)
      (U^(F.widths s.val)) (Real.rpow_pos_of_pos hU _) (hV s.val s.val.property)
      (x s).val (x s).property
    exact base_nonzero_prime F.rowData (x s).val (hp s)
      ((hlarge s.val s.val.property).trans_le hd.2.2.1)
      (fixedBase_zero_unsupported F.rowData.η F.rowData.m F.rowData.f
        F.rowData.lambda_dvd F.rowData.two_dvd (x s).val hn)
  have hprod (T:Finset ↥J):CanonicalQuadraticSieve.Supported (∏s∈T,(x s).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert s T hsT ih =>
      rw [Finset.prod_insert hsT]
      exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs s,ih⟩
  exact ⟨(hprod Finset.univ).1,tuple_product_squarefree _ hp hinj,(hprod Finset.univ).2⟩

omit [NeZero M] in
theorem fiberBase_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)(P:Ideal O) :
    ‖fixedBase F.rowData.η F.rowData.m F.rowData.f P‖≤1 := by
  rw [←baseCharacter_coeff]
  exact idealCoeff_norm_le_one _ _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
