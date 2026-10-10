import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceShift

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorPhysicalSelection
open InverseInitialPhysicalSlots InverseInitialRawDictionary InverseInitialDetectorSource
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open InverseInitialExcludedPeriod CanonicalRowCompletion IdealMobiusDivisorSum InverseMoment
local notation "O"=>HeckeFamily.O

 def actualRow (u:FreeRow):NonzeroElement:=⟨u.val,u.property.1⟩

 theorem actualRow_injective:Function.Injective actualRow:=by
  intro u v he
  exact Subtype.ext (congrArg (fun w:NonzeroElement=>w.val) he)

 theorem actual_rows_sum (rows:Finset FreeRow)(f:NonzeroElement→ℝ):
    (∑u∈rows.image actualRow,f u)=∑u∈rows,f (actualRow u):=
  Finset.sum_image (fun _u _ _v _ h=>actualRow_injective h)

 theorem oriented_child (reverse:Bool)(W:ℝ→ℂ)(v:ℝ):
    orientedProfile reverse (childLogTest W v)=
      childLogTest (orientedProfile reverse W) (orientedFrequency reverse v):=by
  cases reverse
  · rfl
  · exact DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate W v

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem physicalProduct_eq (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(u:FreeRow):
    F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s):=by
  simp only [Fiber.physicalProduct,physical]
  exact (Finset.prod_coe_sort selected _).symm

 theorem fiber_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(σ freq bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H (orientedProfile F.reverse W)
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            σ (orientedFrequency F.reverse freq) bW
            (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hU0:0<U:=zero_lt_one.trans hU
  let mark:NonzeroElement→ℂ:=fun u=>∏s:selected,
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val (F.profile s) (F.upper s)
      (U^(F.widths s)) (F.external s)
  have hw:∀x,orientedProfile F.reverse W x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by cases F.reverse <;> simp [orientedProfile,hz])
  have he:(∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows.image actualRow,‖polynomial (F.rowData.character u) true
        (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq)*mark u‖^2:=by
    rw [actual_rows_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hn:=norm_of_oriented_coefficients (F.family u F.label)
      (F.rowData.character (actualRow u)) F.reverse (F.row_coeff u hu)
      true W (U^F.r) σ freq (Real.rpow_pos_of_pos hU0 _)
    rw [norm_mul,hn,physicalProduct_eq,norm_mul]
    rfl
  rw [he]
  apply (marked_fixed_deletion F.rowData (F.rows.image actualRow)
    (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq) bW
    (Real.rpow_pos_of_pos hU0 _) hw mark).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_rows_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hjpos:0<(j.absNorm:ℝ):=zero_lt_one.trans_le (excluded_divisor_norm F.rowData j hj).1
  have hr:U^(shiftedExponent F.rowData U F.r j)=U^F.r/(j.absNorm:ℝ):=
    by rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 (ne_of_gt hU) hjpos]
  have hn:=deleted_physical_slots_norm_initial F.rowData (actualRow u) M H
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U (shiftedExponent F.rowData U F.r j) σ (orientedFrequency F.reverse freq) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU0 hw (fun s=>hV s s.property)
    (fun s=>hlarge s s.property)
  rw [hr] at hn
  exact congrArg (fun x:ℝ=>x^2) hn

 theorem fiber_child_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(v bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H
            (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            0 0 bW (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hw:∀x,childLogTest W v x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by simp only [childLogTest,hz,zero_mul])
  have hh:=fiber_rows_le_deleted_sources F selected (childLogTest W v) 0 0 bW lower hU hw hV hlarge
  simpa only [oriented_child,orientedFrequency,neg_zero,ite_self] using hh

omit [NeZero M] in
theorem actual_rows_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (u:NonzeroElement)(hu:u∈F.rows.image actualRow):
    ((Ideal.span {u.val}).absNorm:ℝ)≤U:=by
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
  exact F.row_norm v hv

end SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows

end

end OAI
