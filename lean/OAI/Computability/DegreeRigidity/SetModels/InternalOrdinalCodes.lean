import OAI.Computability.DegreeRigidity.Constructibility.InternalOmegaPower
import OAI.Computability.DegreeRigidity.OrdinalCodes.OrdinalSumClosure
import OAI.Computability.DegreeRigidity.OrdinalCodes.OrdinalCodeDomains

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory OrdinalArithmetic RelativeConstructible
universe u

theorem pairCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x y : Ordinal.{u}) (hx : x.toZFSet ∈ M) (hy : y.toZFSet ∈ M) :
    (pairCode x y).toZFSet ∈ M := by
  unfold pairCode
  split
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT x hx))
      (ordinal_omega_opow_internal M hM hT y hy)).1
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_mul_two_internal M hM hT _
        (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT y hy)))
      (ordinal_omega_opow_internal M hM hT x hx)).1

theorem vectorCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    (vectorCode v).toZFSet ∈ M := by
  induction n with
  | zero =>
    simpa only [vectorCode,zero_add] using internal_ordinal_succ M hM hT 0 (internal_ordinal_zero M hM hT)
  | succ n ih =>
    exact pairCode_internal M hM hT _ _ (hv 0) (ih _ (fun i => hv i.succ))

theorem paddedCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (paddedCode v β).toZFSet ∈ M :=
  pairCode_internal M hM hT _ _ hβ (vectorCode_internal M hM hT v hv)

theorem padded_height_index_from_inputs (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (heightDomainIndex (paddedCode v β)).toZFSet ∈ M :=
  padded_height_index_internal M hM hT v β (paddedCode_internal M hM hT v β hv hβ)

theorem internal_padded_codes_cofinal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M)
    (β : Ordinal.{u}) (hβ : β.toZFSet ∈ M) :
    ∃ a : Ordinal.{u}, a.toZFSet ∈ M ∧ β < a ∧ paddedDecode n a = v ∧
      (∀ i, v i < a) ∧ (heightDomainIndex a).toZFSet ∈ M :=
  ⟨paddedCode v β,paddedCode_internal M hM hT v β hv hβ,
    padding_lt_paddedCode v β,paddedDecode_paddedCode v β,entry_lt_paddedCode v β,
    padded_height_index_from_inputs M hM hT v β hv hβ⟩

end TuringRigidity.OrdinalCoding

end OAI
