import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ReturnCountLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SignedAssignedSum

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L n N : ℕ}

structure LineList (D : S.DivisorFamily B τ C₀) (L h ℓ n : ℕ) where
  line : ClosedLine h ℓ
  labels : ∀ i, line.label i ∈ D.members
  primitives : List (AttachedSpec line D L)
  length_le : primitives.length ≤ n

namespace LineList
abbrev RawCode (D : S.DivisorFamily B τ C₀) (ℓ L n : ℕ) :=
  (Fin ℓ → D.members) × (Fin ℓ → Bool) × ListMetadata ℓ L n ×
    (ListCodeSlot L ⌈C₀*Real.log B⌉₊ n → Option S.Index)

noncomputable def rawCode (x : LineList D L h ℓ n) : RawCode D ℓ L n :=
  (fun i => ⟨x.line.label i,x.labels i⟩,signBit x.line,
   listMetadata x.line x.primitives n x.length_le,listPrimeCode x.line x.primitives n)

lemma rawCode_injective : Function.Injective (rawCode : LineList D L h ℓ n → RawCode D ℓ L n) := by
  intro x y hc
  have hlab := congrArg (fun c : RawCode D ℓ L n => c.1) hc
  have hsign := congrArg (fun c : RawCode D ℓ L n => c.2.1) hc
  have hmeta := congrArg (fun c : RawCode D ℓ L n => c.2.2.1) hc
  have hprime := congrArg (fun c : RawCode D ℓ L n => c.2.2.2) hc
  have hl : x.line=y.line := by
    apply GlobalRecord.line_eq_of_labels_signs
    · funext i
      exact congrArg (fun f : Fin ℓ → D.members => (f i).val) hlab
    · funext i
      rw [signBit_decode x.line i,signBit_decode y.line i]
      exact congrArg (fun f : Fin ℓ → Bool => if f i then (1:ℤ) else -1) hsign
  cases x with
  | mk w hw 𝔏 h𝔏 =>
    cases y with
    | mk v hv 𝔐 h𝔐 =>
      dsimp only at hl
      subst v
      have hm : 𝔏=𝔐 := list_code_injective w 𝔏 𝔐 n h𝔏 h𝔐 hmeta hprime
      subst 𝔐
      rfl

instance : Finite (LineList D L h ℓ n) := Finite.of_injective rawCode rawCode_injective
noncomputable instance : Fintype (LineList D L h ℓ n) := Fintype.ofFinite _

noncomputable def retainedSum {T : ℝ} (cut : S.Cutoffs T)
    (G : (x : LineList D L h ℓ n) → S.FixedResidues x.line → Prop) : ℝ :=
  ∑ x : LineList D L h ℓ n, assignedKernelIntegral x.line cut x.primitives (G x)

lemma record_partition (w : ClosedLine h ℓ) (hh : 0 < h) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) :
    (∑ R : AssignedRecord S ℓ,
      assignedKernelIntegral w cut 𝔏 (fun a => G a ∧ recordGroup w hh 𝔏 R a)) =
      assignedKernelIntegral w cut 𝔏 G := by
  unfold assignedKernelIntegral avg
  rw [← mul_sum,sum_comm]
  apply congrArg (fun z : ℝ => (Fintype.card (S.FixedResidues w):ℝ)⁻¹*z)
  apply sum_congr rfl
  intro a ha
  by_cases hG : G a
  · simp only [hG,true_and,ite_true,recordGroup]
    simp
  · simp only [hG,false_and,ite_false,sum_const_zero]

lemma assignedKernelIntegral_nonneg (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) :
    0 ≤ assignedKernelIntegral w cut 𝔏 G := by
  apply avg_nonneg
  intro a
  split_ifs <;> positivity

variable (hh : 0 < h)
variable (G : (x : LineList D L h ℓ n) → S.FixedResidues x.line → Prop)

abbrev SelectedRecord := {z : LineList D L h ℓ n × AssignedRecord S ℓ //
  ∃ a, G z.1 a ∧ recordGroup z.1.line hh z.1.primitives z.2 a}

noncomputable def toGlobal
    (hG : ∀ x a, G x a → Fintype.card (TaggedSlot x.line hh x.primitives a) ≤ N)
    (z : SelectedRecord hh G) : GlobalRecord D L h ℓ hh n N :=
  ⟨z.val.1.line,z.val.1.labels,z.val.1.primitives,z.val.1.length_le,z.val.2,
    by obtain ⟨a,ha,hr⟩ := z.property; exact ⟨a,hr,hG _ a ha⟩⟩

lemma toGlobal_injective
    (hG : ∀ x a, G x a → Fintype.card (TaggedSlot x.line hh x.primitives a) ≤ N) :
    Function.Injective (toGlobal hh G hG) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · apply rawCode_injective
    exact congrArg (fun z : GlobalRecord D L h ℓ hh n N =>
      rawCode (D:=D) (L:=L) (n:=n) ⟨z.line,z.labels,z.primitives,z.length_le⟩) he
  · exact congrArg GlobalRecord.record he

lemma retainedSum_selected {T : ℝ} (cut : S.Cutoffs T) :
    retainedSum cut G = ∑ z : SelectedRecord hh G,
      assignedKernelIntegral z.val.1.line cut z.val.1.primitives
        (fun a => G z.val.1 a ∧ recordGroup z.val.1.line hh z.val.1.primitives z.val.2 a) := by
  unfold retainedSum
  conv_lhs => arg 2; ext x; rw [← record_partition x.line hh cut x.primitives (G x)]
  let f : LineList D L h ℓ n × AssignedRecord S ℓ → ℝ := fun z =>
    assignedKernelIntegral z.1.line cut z.1.primitives
      (fun a => G z.1 a ∧ recordGroup z.1.line hh z.1.primitives z.2 a)
  change (∑ x, ∑ R, f (x,R)) = ∑ z : SelectedRecord hh G, f z.val
  rw [← Fintype.sum_prod_type]
  rw [GlobalRecord.subtype_sum_as_ite]
  apply sum_congr rfl
  intro z hz
  split_ifs with he
  · rfl
  · apply eq_comm.mp
    change (0:ℝ) = assignedKernelIntegral z.1.line cut z.1.primitives _
    unfold assignedKernelIntegral
    have hn : ∀ a, ¬ (G z.1 a ∧ recordGroup z.1.line hh z.1.primitives z.2 a) := by
      intro a ha
      exact he ⟨a,ha⟩
    simp only [hn,ite_false,avg_const]

theorem retainedSum_le_global {T : ℝ} (cut : S.Cutoffs T)
    (hG : ∀ x a, G x a → Fintype.card (TaggedSlot x.line hh x.primitives a) ≤ N) :
    retainedSum cut G ≤ GlobalRecord.signedAssignedSum D L h ℓ hh n N cut := by
  rw [retainedSum_selected hh G cut]
  have hpoint (z : SelectedRecord hh G) :
      assignedKernelIntegral z.val.1.line cut z.val.1.primitives
        (fun a => G z.val.1 a ∧ recordGroup z.val.1.line hh z.val.1.primitives z.val.2 a) ≤
      assignedKernelIntegral (toGlobal hh G hG z).line cut (toGlobal hh G hG z).primitives
        (recordGroup (toGlobal hh G hG z).line hh (toGlobal hh G hG z).primitives
          (toGlobal hh G hG z).record) :=
    assignedKernelIntegral_mono _ _ _ _ _ (fun a ha => ha.2)
  apply (sum_le_sum (fun z hz => hpoint z)).trans
  let f : GlobalRecord D L h ℓ hh n N → ℝ := fun x =>
    assignedKernelIntegral x.line cut x.primitives (recordGroup x.line hh x.primitives x.record)
  change (∑ z, f (toGlobal hh G hG z)) ≤ ∑ x, f x
  rw [← sum_image (fun x _ y _ he => toGlobal_injective hh G hG he)]
  apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
  intro x hx hn
  exact assignedKernelIntegral_nonneg _ _ _ _

end LineList
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
