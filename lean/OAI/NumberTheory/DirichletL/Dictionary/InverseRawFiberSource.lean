import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.DetectorDictionaryInverseRawFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection
local notation "O"=>HeckeFamily.O

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_physical_norm_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖ := by
  have hn:=norm_of_oriented_coefficients (F.family u F.label)
    (F.rowData.character ⟨u.val,u.property.1⟩) F.reverse (F.row_coeff u hu)
    true W (U^F.r) σ t (Real.rpow_pos_of_pos hU _)
  have hp : F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s) := by
    simp only [Fiber.physicalProduct,physical]
    exact (Finset.prod_coe_sort selected _).symm
  rw [norm_mul,hn,←norm_mul,hp]
  have hh:=physical_slots_norm_initial M H F.rowData ⟨u.val,u.property.1⟩
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U F.r σ (orientedFrequency F.reverse t) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU
    (by intro x hx;apply hW x;intro hz;exact hx (by cases F.reverse <;> simp [orientedProfile,hz]))
    (fun s=>hV s s.property) (fun s=>hlarge s s.property)
  convert hh using 1 ; congr 2
  ext p
  simp only [Fintype.mem_piFinset]

theorem fiber_physical_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [fiber_physical_norm_initial F selected W σ t bW lower hU hW hV hlarge u hu]

theorem fiber_inverse_log_upper
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) :
    ∀x,((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) x≠0 → x≤9/4 := by
  induction n with
  | zero =>
    intro x hx
    have hv : HeckeDetectorDyadicProfiles.positiveAnnular x≠0 := by
      intro hz
      exact hx (by simp [Fiber.inverseProfile,HeckeDetectorInverseFiberCount.inverseTest,
        HeckeDetectorDyadicBridge.inverseProfile,hz])
    exact (HeckeDetectorDyadicProfiles.positiveAnnular_support hv).2
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    exact ih x (HeckeDetectorRowwisePolynomial.logProfile_support _ hx)

theorem fiber_inverse_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t : ℝ) (lower : Slot→ℝ)
    (hU : 0<U)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*(9/4)⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  exact fiber_physical_energy_initial F selected
    ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t (9/4) lower
    hU (fiber_inverse_log_upper F n) hV hlarge

end SevenEighths.DetectorDictionaryInverseRawFiberSource

end

end OAI
