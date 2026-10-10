import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchPhysical

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma encode_eq_nil_iff (ws : List (List Bool)) : encode ws=[] ↔ ws=[] := by
  constructor
  · intro h;exact encode_injective h
  · rintro rfl;rfl
end MetricKMedianRecovery.BitMachine.WordList
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
lemma encode_eq_nil_iff {n : ℕ} (S : Finset (Fin n)) : encode S=[] ↔ S=∅ := by
  constructor
  · intro h;exact encode_injective (h.trans (by simp [encode_eq,WordList.encode] : ([] : List Bool)=encode (∅ : Finset (Fin n))))
  · rintro rfl;simp [encode_eq,WordList.encode]
end MetricKMedianRecovery.BitMachine.BinaryFinSet
namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
attribute [local instance] Classical.propDecidable
open WordList WordOperations BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
lemma outside_nil : outside data=[] ↔ s.deleted⊆S := by
  rw [outside_pack,BinaryFinSet.encode_eq_nil_iff,Finset.sdiff_eq_empty_iff_subset]
lemma badBalls_nil : badBalls data=[] ↔ ∀ i,(balls δ F s i).Nonempty := by
  rw [badBalls_pack,encode_eq_nil_iff]
  simp only [List.filter_eq_nil_iff,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    decide_eq_true_eq,BinaryFinSet.encode_eq_nil_iff,←Finset.nonempty_iff_ne_empty]
lemma badRadii_nil : badRadii data=[] ↔ ∀ z∈s.leaves,0≤z.2 := by
  rw [badRadii_pack,BinaryNearestLeaf.leavesBits,encode_eq_nil_iff]
  simp only [List.map_eq_nil_iff,List.filter_eq_nil_iff,decide_eq_true_eq,not_lt]
lemma run_pack : run data=decide (Ready δ F S s colors k c m) := by
  have hc:=classOf_pack δ D F S Δ s colors label k c extra (1:Fin 3)
  change classOf 1 data=_ at hc
  unfold run Ready
  simp only [outside_nil,badBalls_nil,badRadii_nil,lhs_pack,rhs_pack,value_bits,
    hc,BinaryFinSet.encode_lengthBits]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,value_bits]
  congr 1
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y] [Fintype L]
lemma best_some_of_plan (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (P : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c) :
    ∃ v xs,best (block B F label q) c Finset.univ=some (v,xs) := by
  have hh:=optimizer_value B F label q c Finset.univ
  cases he : best (block B F label q) c Finset.univ with
  | none=>
    rw [he,value,←P.value_eq] at hh
    exact False.elim (WithTop.coe_ne_top hh.symm)
  | some x=>exact ⟨x.1,x.2,rfl⟩
omit [LinearOrder R] in
lemma plan_value_unique (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (P Q : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c) :
    (∑ l,(q (P.sel l) (P.dst l):ℝ))=∑ l,(q (Q.sel l) (Q.dst l):ℝ) := by
  exact WithTop.coe_injective (P.value_eq.trans Q.value_eq.symm)
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open Categorical.Explicit
open MetricKMedianRecovery.Categorical
variable {q a p r : ℕ}
attribute [local irreducible] BinaryCategorical.rule exponent samples
lemma choices_binary (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) :
    (choices k base distance weight redBase redDistance part hp
      (binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)).toFinset=
    Selected.binaryGreedyOutput part (BinaryCategorical.rule part hp)
      (Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))) bits := by
  rw [choices_toFinset]
  have he : (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ))=
      Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) := by
    funext S
    exact BinaryCompletion.savingQ_cast K k base distance weight redBase redDistance S
  rw [he]
  rfl
lemma sixtyTwoFin (part : Fin q→Fin a) (rule : Selected.Rule part) (g : SetFunction (Fin q))
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅=0)
    (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
    (62/100:ℝ)*g X ≤ FiniteSampling.average
      (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
        g (Selected.binaryGreedyOutput part rule g bits)) := by
  by_cases ha : 0<a
  · have hh:=Selected.binaryGreedyOutput_expected (b:=exponent a) (L:=samples q a) part rule g hmono hsub hg0 ha
      (show (0:ℝ)<1/1000 by norm_num) (by norm_num) (by simpa only [steps] using scale a)
      (samples_pos q a) (by simpa only [steps,Fintype.card_fin] using count q a) X hX
    have he : 1/Real.exp 1 ≤ (37/100:ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9]
    have hn : 0 ≤ g X := by rw [←hg0]; exact hmono (Finset.empty_subset _)
    exact (mul_le_mul_of_nonneg_right (by linarith : (62/100:ℝ) ≤ 1-1/Real.exp 1-4*(1/1000)) hn).trans hh
  · have hE : IsEmpty (Fin q) := ⟨fun e=>by have := (part e).isLt; omega⟩
    have hX0 : X=∅ := Subsingleton.elim _ _
    rw [hX0,hg0,mul_zero]
    apply FiniteSampling.average_nonneg
    intro bits
    rw [Subsingleton.elim (Selected.binaryGreedyOutput part rule g bits) ∅,hg0]
lemma choices_expected (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part) (hw : ∀ i,0≤weight i)
    (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
    FiniteSampling.average (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
      Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))
        (choices k base distance weight redBase redDistance part hp
          (binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)).toFinset) ≤
      (38/100:ℝ)*Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
      (62/100:ℝ)*Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X := by
  simp_rw [choices_binary K]
  let b : Fin p→ℝ := fun i=>(base i:ℝ)
  let d : Fin p→Fin q→ℝ := fun i e=>(distance i e:ℝ)
  let w : Fin r→ℝ := fun i=>(weight i:ℝ)
  let rb : Fin r→ℝ := fun i=>(redBase i:ℝ)
  let rd : Fin r→Fin q→ℝ := fun i e=>(redDistance i e:ℝ)
  have hw' : ∀ i,0≤w i := fun i=>Rat.cast_nonneg.mpr (hw i)
  have hh:=sixtyTwoFin part (BinaryCategorical.rule part hp) (Completion.saving K k b d w rb rd)
    (Completion.saving_mono K k b d w rb rd hw')
    (fun Y Z hYZ e=>Completion.saving_diminishing K k b d w rb rd hw' hYZ e)
    (Completion.saving_empty K k b d w rb rd) X hX
  simp only [Completion.saving,FiniteSampling.average_sub,FiniteSampling.average_const] at hh
  change _ ≤ 38/100*Completion.surrogate K k b d w rb rd ∅+62/100*Completion.surrogate K k b d w rb rd X
  linarith

end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
