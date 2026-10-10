import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UsedPrimeReciprocal
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UntaggedReferenceWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L n N : ℕ}

structure GlobalRecord (D : S.DivisorFamily B τ C₀) (L h ℓ : ℕ) (hh : 0 < h) (n N : ℕ) where
  line : ClosedLine h ℓ
  labels : ∀ i, line.label i ∈ D.members
  primitives : List (AttachedSpec line D L)
  length_le : primitives.length ≤ n
  record : AssignedRecord S ℓ
  realized : ∃ a : S.FixedResidues line,
    recordAt line hh primitives a=record ∧ Fintype.card (TaggedSlot line hh primitives a) ≤ N

namespace GlobalRecord
variable {hh : 0 < h}

lemma line_eq_of_labels_signs (w v : ClosedLine h ℓ)
    (hl : w.label=v.label) (hs : w.sign=v.sign) : w=v := by
  have ho : w.offset=v.offset := by
    funext j
    induction j using Fin.induction with
    | zero => rw [w.start_zero,v.start_zero]
    | succ i ih =>
      have hw := w.step i
      have hv := v.step i
      rw [hl,hs] at hw
      linarith only [hw,hv,ih]
  exact ClosedLine.ext_values w v ho hl hs

abbrev RawCode (D : S.DivisorFamily B τ C₀) (ℓ L n : ℕ) :=
  (Fin ℓ → D.members) × (Fin ℓ → Bool) × ListMetadata ℓ L n ×
    (ListCodeSlot L ⌈C₀*Real.log B⌉₊ n → Option S.Index) × AssignedRecord S ℓ

noncomputable def rawCode (x : GlobalRecord D L h ℓ hh n N) : RawCode D ℓ L n :=
  (fun i => ⟨x.line.label i,x.labels i⟩,signBit x.line,
   listMetadata x.line x.primitives n x.length_le,listPrimeCode x.line x.primitives n,x.record)

lemma rawCode_injective : Function.Injective (rawCode : GlobalRecord D L h ℓ hh n N → RawCode D ℓ L n) := by
  intro x y hc
  have hlabel := congrArg (fun c : RawCode D ℓ L n => c.1) hc
  have hsign := congrArg (fun c : RawCode D ℓ L n => c.2.1) hc
  have hmeta := congrArg (fun c : RawCode D ℓ L n => c.2.2.1) hc
  have hprime := congrArg (fun c : RawCode D ℓ L n => c.2.2.2.1) hc
  have hrec := congrArg (fun c : RawCode D ℓ L n => c.2.2.2.2) hc
  have hl : x.line=y.line := by
    apply line_eq_of_labels_signs
    · funext i
      exact congrArg (fun f : Fin ℓ → D.members => (f i).val) hlabel
    · funext i
      rw [signBit_decode x.line i,signBit_decode y.line i]
      exact congrArg (fun f : Fin ℓ → Bool => if f i then (1:ℤ) else -1) hsign
  cases x with
  | mk w hw 𝔏 h𝔏 R hR =>
    cases y with
    | mk v hv 𝔐 h𝔐 T hT =>
      dsimp only at hl
      subst v
      have hm : 𝔏=𝔐 := list_code_injective w 𝔏 𝔐 n h𝔏 h𝔐 hmeta hprime
      subst 𝔐
      change R=T at hrec
      subst T
      rfl

instance : Finite (GlobalRecord D L h ℓ hh n N) := Finite.of_injective rawCode rawCode_injective
noncomputable instance : Fintype (GlobalRecord D L h ℓ hh n N) := Fintype.ofFinite _

noncomputable def majorantSum (T err : ℝ) : ℝ :=
  ∑ x : GlobalRecord D L h ℓ hh n N, traceIntegrationMajorant x.line hh x.primitives x.record T err

def Fiber (r : ℕ) (t : Topology ℓ r) :=
  {x : GlobalRecord D L h ℓ hh n N // ∃ hr : (returnSteps x.line).card=r,
    encodeTopology x.line r hr=t}

noncomputable instance (r : ℕ) (t : Topology ℓ r) : Fintype (Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t) :=
  by unfold Fiber; infer_instance

noncomputable def toPacket {r : ℕ} {t : Topology ℓ r}
    (x₀ : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t)
    (x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t) :
    RecordPacket D L x₀.val.line hh r x₀.property.choose n N :=
  ⟨x.val.line,x.val.labels,x.property.choose,
    x.property.choose_spec.trans x₀.property.choose_spec.symm,
    x.val.primitives,x.val.length_le,x.val.record,x.val.realized⟩

lemma toPacket_injective {r : ℕ} {t : Topology ℓ r}
    (x₀ : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t) :
    Function.Injective (toPacket x₀) := by
  intro x y he
  apply Subtype.ext
  apply rawCode_injective
  exact congrArg (fun z : RecordPacket D L x₀.val.line hh r x₀.property.choose n N =>
    rawCode (D:=D) (hh:=hh) (N:=N) ⟨z.line,z.labels,z.primitives,z.length_le,z.record,z.realized⟩) he

lemma fiber_sum_le (r : ℕ) (t : Topology ℓ r)
    (x₀ : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t) (T err : ℝ) :
    (∑ x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t,
      traceIntegrationMajorant x.val.line hh x.val.primitives x.val.record T err) ≤
    ∑ x : RecordPacket D L x₀.val.line hh r x₀.property.choose n N,
      traceIntegrationMajorant x.line hh x.primitives x.record T err := by
  let f := fun x : RecordPacket D L x₀.val.line hh r x₀.property.choose n N =>
    traceIntegrationMajorant x.line hh x.primitives x.record T err
  change (∑ x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t, f (toPacket x₀ x)) ≤ _
  rw [← sum_image (fun x _ y _ hxy => toPacket_injective x₀ hxy)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => traceIntegrationMajorant_nonneg ..)

end GlobalRecord
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
