import Mathlib
import OAI.Probability.Contingency.ConcreteContexts

namespace OAI

/-! Conditional Transport. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}
variable (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))

noncomputable def repairedChild (j : ℕ) (t : Fin a) : ℕ :=
  if (suffixSlot U r c k a h t.succ).val.1=(suffixSlot U r c k a h 0).val.1 then j+1 else j

abbrev FeasibleBranches (j : ℕ) (t : Fin a) :=
  {α : ∀ v, Fin (surplusCaps U a t v+1) // Feasible U r c (defectState U r c k a h σ j t α)}

noncomputable instance feasibleBranchesFintype (j : ℕ) (t : Fin a) :
    Fintype (FeasibleBranches U r c k a h σ j t) := by
  classical
  unfold FeasibleBranches
  infer_instance

noncomputable def repairedBranch (j : ℕ) (t : Fin a) (α : FeasibleBranches U r c k a h σ j t) :
    Fin a → Fin (U+1) :=
  stateSuffix U r c k a h
    (repair U r c (suffixSlot U r c k a h 0).val (suffixSlot U r c k a h t.succ).val
      (defectState U r c k a h σ j t α.val))
    (repair_feasible U r c _ _ _ α.property (defectState_defect U r c k a h σ j t α.val))

theorem repairedBranch_state (j : ℕ) (t : Fin a) (α : FeasibleBranches U r c k a h σ j t) :
    contextState U r c k a h σ (mixedDisplay a (fun _ => U)
      (childProfile U (repairedChild U r c k a h j t)) (repairedBranch U r c k a h σ j t α)) =
    repair U r c (suffixSlot U r c k a h 0).val (suffixSlot U r c k a h t.succ).val
      (defectState U r c k a h σ j t α.val) := by
  apply contextState_reconstruct
  · exact repair_transversal U r c _ _ _
  · intro v
    have hp := repair_prefix U r c _ _ _ (defectState_defect U r c k a h σ j t α.val)
      (suffix_before U r c k a h 0 t.succ (Fin.succ_pos t))
      (prefixSlot U r c k a h v).val (prefix_before_suffix U r c k a h v 0)
    exact hp.1.trans (contextState_prefix U r c k a h σ _ v).1
  · have hs := repair_special U r c _ _ _ (defectState_defect U r c k a h σ j t α.val)
      ((j:ℤ)+1) (by simp)
    simpa only [repairedChild, Nat.cast_ite,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hs

theorem repairedBranch_injective (j : ℕ) (t : Fin a) :
    Function.Injective (repairedBranch U r c k a h σ j t) := by
  intro α β he
  apply Subtype.ext
  have hs := congrArg (fun v => contextState U r c k a h σ (mixedDisplay a (fun _ => U)
    (childProfile U (repairedChild U r c k a h j t)) v)) he
  rw [repairedBranch_state,repairedBranch_state] at hs
  have hx := repair_injective U r c _ _ _ _ (defectState_defect U r c k a h σ j t α.val)
    (defectState_defect U r c k a h σ j t β.val) hs
  exact mixedDisplay_injective a _ _ (contextState_injective U r c k a h σ hx)

 

theorem mixedBalance_repair (hrc : (∑ i, r i)=∑ j, c j)
    (hC : ∀ i, paddedRow U L r c i ≤ C) (j : ℕ) (t : Fin a) :
    mixedBalance a (surplusCaps U a t) (contextKernel 0 U L C r c k a h σ) (defectProfile U j) ≤
      nodeMass U a (contextKernel 0 U L C r c k a h σ) (repairedChild U r c k a h j t) := by
  classical
  let P : (∀ v, Fin (surplusCaps U a t v+1)) → Prop :=
    fun α => Feasible U r c (defectState U r c k a h σ j t α)
  let F := fun α => contextKernel 0 U L C r c k a h σ
    (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α)
  let G := fun β => contextKernel 0 U L C r c k a h σ
    (mixedDisplay a (fun _ => U) (childProfile U (repairedChild U r c k a h j t)) β)
  have h0 (α : ∀ v, Fin (surplusCaps U a t v+1)) (hα : ¬P α) : F α=0 :=
    smallKernel_zero_infeasible U L C r c _ hα
  have hsum : (∑ α : FeasibleBranches U r c k a h σ j t, F α.val) = ∑ α, F α := by
    have he := Fintype.sum_subtype_add_sum_subtype P F
    have hz : (∑ α : {α // ¬P α}, F α.val)=0 :=
      Finset.sum_eq_zero fun α _ => h0 α.val α.property
    rw [hz,add_zero] at he
    exact he
  have hle (α : FeasibleBranches U r c k a h σ j t) :
      F α.val ≤ G (repairedBranch U r c k a h σ j t α) := by
    dsimp [F,G]
    rw [contextKernel_weight U L C r c hrc hC,contextKernel_weight U L C r c hrc hC,
      repairedBranch_state]
    exact_mod_cast weight_repair_le U L r c _ _ _ (defectState_defect U r c k a h σ j t α.val)
  have hg (β : Fin a → Fin (U+1)) : 0 ≤ G β := contextKernel_nonneg U L C r c k a h σ _
  change (∑ α, F α) ≤ _
  rw [← hsum]
  change _ ≤ allBalance U a (contextKernel 0 U L C r c k a h σ)
    (childProfile U (repairedChild U r c k a h j t))
  rw [allBalance_mixed]
  change _ ≤ ∑ β, G β
  calc
    _ ≤ ∑ α : FeasibleBranches U r c k a h σ j t, G (repairedBranch U r c k a h σ j t α) :=
      Finset.sum_le_sum fun α _ => hle α
    _ = ∑ β ∈ Finset.univ.image (repairedBranch U r c k a h σ j t), G β := by
      rw [Finset.sum_image (fun x _ y _ he => repairedBranch_injective U r c k a h σ j t he)]
    _ ≤ ∑ β, G β := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun β _ _ => hg β)

theorem mixedBalance_repair_max (hrc : (∑ i, r i)=∑ j, c j)
    (hC : ∀ i, paddedRow U L r c i ≤ C) (j : ℕ) (t : Fin a) :
    mixedBalance a (surplusCaps U a t) (contextKernel 0 U L C r c k a h σ) (defectProfile U j) ≤
      max (nodeMass U a (contextKernel 0 U L C r c k a h σ) j)
        (nodeMass U a (contextKernel 0 U L C r c k a h σ) (j+1)) := by
  have hh := mixedBalance_repair U L C r c k a h σ hrc hC j t
  unfold repairedChild at hh
  split_ifs at hh
  · exact hh.trans (le_max_right _ _)
  · exact hh.trans (le_max_left _ _)

theorem context_auxiliary_bound (hrc : (∑ i, r i)=∑ j, c j)
    (hC : ∀ i, paddedRow U L r c i ≤ C) (j : ℕ) :
    auxiliaryMass a U (contextKernel 0 U L C r c k a h σ) (adjacentDisplay U j) ≤
      (a:ℝ)*max (nodeMass U a (contextKernel 0 U L C r c k a h σ) j)
        (nodeMass U a (contextKernel 0 U L C r c k a h σ) (j+1)) := by
  rw [auxiliaryMass,adjacent_removePair,allSurplus_sum_types]
  calc
    _ ≤ ∑ t : Fin a, max (nodeMass U a (contextKernel 0 U L C r c k a h σ) j)
        (nodeMass U a (contextKernel 0 U L C r c k a h σ) (j+1)) :=
      Finset.sum_le_sum fun t _ => mixedBalance_repair_max U L C r c k a h σ hrc hC j t
    _ = _ := by simp

theorem concrete_conditional_transport (hU : 2 ≤ U) (hC2 : 2 ≤ C)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : (PairCoords Bool a → ℤ) → ℝ) (j : ℕ) (hj : j<U) :
    min (nodeMass U a (contextKernel 0 U L C r c k a h σ) j)
      (nodeMass U a (contextKernel 0 U L C r c k a h σ) (j+1)) *
      (nodeMean U a (contextKernel 0 U L C r c k a h σ) H j-
        nodeMean U a (contextKernel 0 U L C r c k a h σ) H (j+1))^2 ≤
      (2+2*(a:ℝ)*((U:ℝ)+1)^2) * ∑ e ∈ smallUnitEdges U a,
        edgeEnergy (contextKernel 0 U L C r c k a h σ) H e :=
  node_adjacent_bound U hU a _ (contextKernel_continuous U L C r c k a h σ)
    (fun η hη hη' => (contextKernel_signature η hη hη' U L C hC2 r c k a h σ).1)
    (fun η hη hη' => (contextKernel_signature η hη hη' U L C hC2 r c k a h σ).2)
    (contextKernel_nonneg U L C r c k a h σ) H a (by positivity) j hj
    (context_auxiliary_bound U L C r c k a h σ hrc hC j)

 

theorem concrete_node_variance (hU : 2 ≤ U) (hC2 : 2 ≤ C)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : (PairCoords Bool a → ℤ) → ℝ) :
    weightedVariance (fun j : Fin (U+1) => nodeMass U a (contextKernel 0 U L C r c k a h σ) j)
      (fun j => nodeMean U a (contextKernel 0 U L C r c k a h σ) H j) ≤
      ((U:ℝ)+1)^4*(2+2*(a:ℝ)*((U:ℝ)+1)^2) * ∑ e ∈ smallUnitEdges U a,
        edgeEnergy (contextKernel 0 U L C r c k a h σ) H e := by
  apply node_variance_bound
  · intro j hj
    exact allBalance_nonneg U a _ (contextKernel_nonneg U L C r c k a h σ) _
  · positivity
  · exact Finset.sum_nonneg fun e _ =>
      edgeEnergy_nonneg _ H (contextKernel_nonneg U L C r c k a h σ) e
  · exact context_child_no_holes U L C hU hC2 r c k a h σ
  · exact concrete_conditional_transport U L C r c k a h σ hU hC2 hrc hC H

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency

noncomputable def profileEquiv (C : ℕ) : (n : ℕ) → Profiles C n ≃ (Fin n → Fin (C+1))
  | 0 => { toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => PUnit.unit
           left_inv := fun x => by cases x; rfl
           right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n+1 => ((Equiv.refl (Fin (C+1))).prodCongr (profileEquiv C n)).trans
      (piHeadEquiv (fun _ : Fin (n+1) => Fin (C+1))).symm

@[simp] theorem profileEquiv_succ (C n : ℕ) (j : Fin (C+1)) (α : Profiles C n) :
    profileEquiv C (n+1) (j,α) = Fin.cons j (profileEquiv C n α) := rfl

namespace PaddedGraph
variable {m n : ℕ}

noncomputable def tupleState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (α : SmallSlot U r c → Fin (U+1)) : State m n :=
  coordinatesState U r c (fun w => if w.2 then (α w.1:ℕ) else (U:ℤ)-(α w.1:ℕ))

@[simp] theorem tupleState_x (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (α : SmallSlot U r c → Fin (U+1)) (s : SmallSlot U r c) :
    (tupleState U r c α).x s.val=(α s:ℕ) := by simp [tupleState]

@[simp] theorem tupleState_q (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (α : SmallSlot U r c → Fin (U+1)) (s : SmallSlot U r c) :
    (tupleState U r c α).q s.val=(α s:ℕ) := by simp [tupleState]

noncomputable def appendAssignment (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+a)
    (σ : Fin k → Fin (U+1)) (τ : Fin a → Fin (U+1)) : SmallSlot U r c → Fin (U+1) :=
  Fin.append σ τ ∘ finCongr h ∘ (smallIndex U r c).symm

@[simp] theorem appendAssignment_prefix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (τ : Fin (a+1) → Fin (U+1)) (s : Fin k) :
    appendAssignment U r c k (a+1) h σ τ (prefixSlot U r c k a h s)=σ s := by
  simp only [appendAssignment,Function.comp_apply,prefixSlot,splitSlots,Equiv.symm_trans_apply,
    Equiv.symm_symm,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  exact Fin.append_left σ τ s

@[simp] theorem appendAssignment_suffix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (τ : Fin (a+1) → Fin (U+1)) (s : Fin (a+1)) :
    appendAssignment U r c k (a+1) h σ τ (suffixSlot U r c k a h s)=τ s := by
  simp only [appendAssignment,Function.comp_apply,suffixSlot,splitSlots,Equiv.symm_trans_apply,
    Equiv.symm_symm,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  exact Fin.append_right σ τ s

@[simp] theorem appendAssignment_cons (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (j : Fin (U+1)) (τ : Fin a → Fin (U+1)) :
    appendAssignment U r c k (a+1) h σ (Fin.cons j τ) =
      appendAssignment U r c (k+1) a (by omega) (Fin.snoc σ j) τ := by
  funext s
  simp only [appendAssignment,Function.comp_apply,Fin.append_right_cons]
  rfl

 

noncomputable def profileState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+a) (σ : Fin k → Fin (U+1))
    (τ : Profiles U a) : State m n :=
  tupleState U r c (appendAssignment U r c k a h σ (profileEquiv U a τ))

@[simp] theorem profileState_succ (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (j : Fin (U+1)) (τ : Profiles U a) :
    profileState U r c k (a+1) h σ (j,τ) =
      profileState U r c (k+1) a (by omega) (Fin.snoc σ j) τ := by
  simp only [profileState,profileEquiv_succ,appendAssignment_cons]

 

theorem contextState_profile (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (j : Fin (U+1)) (τ : Profiles U a) :
    contextState U r c k a h σ
      (mixedDisplay a (fun _ => U) (childProfile U j) (profileEquiv U a τ)) =
    profileState U r c k (a+1) h σ (j,τ) := by
  apply State.ext <;> funext w
  all_goals
    by_cases hw : IsSmall U r c w
    · rcases slot_cases U r c k a h ⟨w,hw⟩ with ⟨s,hs⟩ | ⟨s,hs⟩
      · have he : w = _ := congrArg Subtype.val hs
        subst w
        simp only [profileState,profileEquiv_succ,tupleState_x,tupleState_q,
          appendAssignment_prefix]
        first | exact (contextState_prefix U r c k a h σ _ s).1 |
          exact (contextState_prefix U r c k a h σ _ s).2
      · have he : w = _ := congrArg Subtype.val hs
        subst w
        simp only [profileState,profileEquiv_succ,tupleState_x,tupleState_q,
          appendAssignment_suffix]
        first
        | rw [(contextState_suffix U r c k a h σ _ s).1]
        | rw [(contextState_suffix U r c k a h σ _ s).2]
        all_goals
          refine Fin.cases ?_ (fun v => ?_) s
          · simp [mixedDisplay_current,childProfile]
          · simp [mixedDisplay_ordinary]
    · have hl : IsLarge U r c w := Classical.not_not.mp hw
      have h1 := contextState_supported U r c k a h σ
        (mixedDisplay a (fun _ => U) (childProfile U j) (profileEquiv U a τ)) w hl
      have h2 := coordinatesState_supported U r c
        (fun w => if w.2 then
          (appendAssignment U r c k (a+1) h σ (profileEquiv U (a+1) (j,τ)) w.1:ℕ)
          else (U:ℤ)-(appendAssignment U r c k (a+1) h σ (profileEquiv U (a+1) (j,τ)) w.1:ℕ)) w hl
      first | exact h1.1.trans h2.1.symm | exact h1.2.trans h2.2.symm

theorem nodeMass_profile (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (j : Fin (U+1)) :
    nodeMass U a (contextKernel 0 U L C r c k a h σ) j =
      totalWeight (fun τ : Profiles U a =>
        (weight U L r c (profileState U r c k (a+1) h σ (j,τ)):ℝ)) := by
  rw [nodeMass,allBalance_mixed]
  unfold mixedBalance totalWeight
  rw [← Equiv.sum_comp (profileEquiv U a)]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [contextKernel_weight U L C r c hrc hC,contextState_profile]

theorem nodeMean_profile (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (H : State m n → ℝ) (j : Fin (U+1)) :
    nodeMean U a (contextKernel 0 U L C r c k a h σ)
      (H ∘ contextState U r c k a h σ) j =
    weightedMean (fun τ : Profiles U a =>
      (weight U L r c (profileState U r c k (a+1) h σ (j,τ)):ℝ))
      (fun τ => H (profileState U r c k (a+1) h σ (j,τ))) := by
  rw [nodeMean,nodeMass_profile U L C r c hrc hC]
  unfold weightedMean
  congr 1
  rw [nodeMass,allBalance_mixed]
  unfold mixedBalance
  rw [← Equiv.sum_comp (profileEquiv U a)]
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [Function.comp_apply,contextKernel_weight U L C r c hrc hC,contextState_profile]

end PaddedGraph
end Contingency

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

noncomputable def contextEnergy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (H : State m n → ℝ) : ℝ :=
  ∑ e ∈ smallUnitEdges U a, edgeEnergy (contextKernel 0 U L C r c k a h σ)
    (H ∘ contextState U r c k a h σ) e

theorem contextEnergy_nonneg (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (H : State m n → ℝ) : 0 ≤ contextEnergy U L C r c k a h σ H :=
  Finset.sum_nonneg fun e _ => edgeEnergy_nonneg _ _ (contextKernel_nonneg U L C r c k a h σ) e

noncomputable def contextTree (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : (a k : ℕ) →
      (h : Fintype.card (SmallSlot U r c)=k+a) → (Fin k → Fin (U+1)) → ExposureEnergies U a
  | 0, _, _, _ => PUnit.unit
  | a+1, k, h, σ => (contextEnergy U L C r c k a h σ H,
      fun j => contextTree U L C r c H a (k+1) (by omega) (Fin.snoc σ j))

theorem local_constant_le (U d a : ℕ) (_hd : 1 ≤ d) (ha : a<d) :
    ((U:ℝ)+1)^4*(2+2*(a:ℝ)*((U:ℝ)+1)^2) ≤ 4*(d:ℝ)*((U:ℝ)+1)^6 := by
  have hU : 1 ≤ ((U:ℝ)+1)^2 := by nlinarith [show 0 ≤ (U:ℝ) by positivity]
  have had : (a:ℝ)+1 ≤ d := by exact_mod_cast ha
  have h1 : 2+2*(a:ℝ)*((U:ℝ)+1)^2 ≤ 4*(d:ℝ)*((U:ℝ)+1)^2 := by
    have ha0 : 0 ≤ (a:ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right had (show 0 ≤ ((U:ℝ)+1)^2 by positivity)
    nlinarith
  calc
    _ ≤ ((U:ℝ)+1)^4*(4*(d:ℝ)*((U:ℝ)+1)^2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem contextTree_childBounds (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hU : 2 ≤ U) (hC2 : 2 ≤ C) (hd : 1 ≤ d) (hslots : Fintype.card (SmallSlot U r c) ≤ d)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) (a k : ℕ) (h : Fintype.card (SmallSlot U r c)=k+a)
    (σ : Fin k → Fin (U+1)) :
    ChildVarianceBounds U (4*(d:ℝ)*((U:ℝ)+1)^6) a
      (fun τ => (weight U L r c (profileState U r c k a h σ τ):ℝ))
      (fun τ => H (profileState U r c k a h σ τ))
      (contextTree U L C r c H a k h σ) := by
  induction a generalizing k with
  | zero => trivial
  | succ a ih =>
    constructor
    · change weightedVariance
        (fun j => totalWeight (fun τ : Profiles U a =>
          (weight U L r c (profileState U r c k (a+1) h σ (j,τ)):ℝ)))
        (fun j => weightedMean
          (fun τ : Profiles U a => (weight U L r c (profileState U r c k (a+1) h σ (j,τ)):ℝ))
          (fun τ => H (profileState U r c k (a+1) h σ (j,τ)))) ≤
            (4*(d:ℝ)*((U:ℝ)+1)^6)*contextEnergy U L C r c k a h σ H
      simp_rw [← nodeMass_profile U L C r c hrc hC, ← nodeMean_profile U L C r c hrc hC]
      have hb := concrete_node_variance U L C r c k a h σ hU hC2 hrc hC
        (H ∘ contextState U r c k a h σ)
      exact hb.trans (mul_le_mul_of_nonneg_right (local_constant_le U d a hd (by omega))
        (contextEnergy_nonneg U L C r c k a h σ H))
    · intro j
      simpa only [profileState_succ,contextTree] using ih (k+1) (by omega) (Fin.snoc σ j)

 

theorem concrete_exposure_variance (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hU : 2 ≤ U) (hC2 : 2 ≤ C) (hd : 1 ≤ d) (hslots : Fintype.card (SmallSlot U r c) ≤ d)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) (a k : ℕ) (h : Fintype.card (SmallSlot U r c)=k+a)
    (σ : Fin k → Fin (U+1)) :
    weightedVariance
      (fun τ => (weight U L r c (profileState U r c k a h σ τ):ℝ))
      (fun τ => H (profileState U r c k a h σ τ)) ≤
      4*(d:ℝ)*((U:ℝ)+1)^6 * exposureEnergy U a (contextTree U L C r c H a k h σ) :=
  exposure_variance_bound U _ a _ _ (fun τ => by positivity) _
    (contextTree_childBounds U L C d r c hU hC2 hd hslots hrc hC H a k h σ)

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

noncomputable def fullOccupancy (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) (s : SmallSlot U r c) : ℤ := p (s,true)+p (s,false)

def fullPattern (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) : Prop :=
  (∀ s, fullOccupancy U r c p s=U) ∨
  ∃ s t, s≠t ∧ fullOccupancy U r c p s=(U:ℤ)-1 ∧ fullOccupancy U r c p t=(U:ℤ)+1 ∧
    ∀ v, v≠s → v≠t → fullOccupancy U r c p v=U

noncomputable def fullVertices (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finset (SmallCoord U r c → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ => Finset.Icc 0 (U:ℤ))).filter (fullPattern U r c)

theorem mem_fullVertices (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (p : SmallCoord U r c → ℤ) :
    p∈fullVertices U r c ↔ InBox (fun _ => (U:ℤ)) p ∧ fullPattern U r c p := by
  classical
  simp [fullVertices,Fintype.mem_piFinset,InBox]

 

noncomputable def fullUnitEdges (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finset (Sym2 (SmallCoord U r c → ℤ)) := by
  classical
  exact (fullVertices U r c).sym2.filter (fun e => ∃ D i j, i≠j ∧
    e=s(removeOne D i,removeOne D j))

noncomputable def contextDisplay (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) : SmallCoord U r c → ℤ :=
  Sum.elim (balanceProfile (fun _ => U) σ) p ∘ contextCoordinates U r c k a h

@[simp] theorem contextDisplay_prefix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (s : Fin k) (b : Bool) :
    contextDisplay U r c k a h σ p (prefixSlot U r c k a h s,b) =
      if b then ((σ s:ℕ):ℤ) else (U:ℤ)-(σ s:ℕ) := by simp [contextDisplay,balanceProfile]

@[simp] theorem contextDisplay_suffix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (s : Fin (a+1)) (b : Bool) :
    contextDisplay U r c k a h σ p (suffixSlot U r c k a h s,b) =
      p ((smallCoords a).symm (s,b)) := by simp [contextDisplay]

theorem contextDisplay_joint_inj (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1))
    (σ τ : Fin k → Fin (U+1)) (p q : PairCoords Bool a → ℤ)
    (he : contextDisplay U r c k a h σ p=contextDisplay U r c k a h τ q) : σ=τ ∧ p=q := by
  constructor
  · funext s
    have hh := congrFun he (prefixSlot U r c k a h s,true)
    simp only [contextDisplay_prefix,ite_true] at hh
    apply Fin.ext
    exact_mod_cast hh
  · funext i
    have hh := congrFun he ((contextCoordinates U r c k a h).symm (.inr i))
    simpa [contextDisplay] using hh

theorem contextDisplay_box (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (hp : InBox (fun _ => (U:ℤ)) p) :
    InBox (fun _ => (U:ℤ)) (contextDisplay U r c k a h σ p) := by
  intro w
  obtain ⟨z,rfl⟩ := (contextCoordinates U r c k a h).symm.surjective w
  cases z with
  | inl z => simpa [contextDisplay] using balanceProfile_box U k σ z
  | inr z => simpa [contextDisplay] using hp z

theorem contextDisplay_pattern (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (hp : smallPattern U a p) :
    fullPattern U r c (contextDisplay U r c k a h σ p) := by
  have hpre (s : Fin k) : fullOccupancy U r c (contextDisplay U r c k a h σ p)
      (prefixSlot U r c k a h s)=U := by simp [fullOccupancy]
  have hsuf (s : Fin (a+1)) : fullOccupancy U r c (contextDisplay U r c k a h σ p)
      (suffixSlot U r c k a h s)=smallOccupancy a p s := by simp [fullOccupancy,smallOccupancy]
  rcases hp with ht | ⟨s,t,hst,hs,ht,hrest⟩
  · left
    intro w
    rcases slot_cases U r c k a h w with ⟨s,rfl⟩ | ⟨s,rfl⟩
    · exact hpre s
    · rw [hsuf,ht]
  · right
    refine ⟨suffixSlot U r c k a h s,suffixSlot U r c k a h t,?_,?_,?_,?_⟩
    · intro he
      have hh := congrArg Subtype.val he
      exact hst ((suffixSlot_val_inj U r c k a h s t).mp hh)
    · rw [hsuf,hs]
    · rw [hsuf,ht]
    · intro w hws hwt
      rcases slot_cases U r c k a h w with ⟨v,rfl⟩ | ⟨v,rfl⟩
      · exact hpre v
      · rw [hsuf]
        exact hrest v (fun he => hws (congrArg _ he)) (fun he => hwt (congrArg _ he))

theorem contextDisplay_vertex (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (hp : p∈smallVertexSet U a) :
    contextDisplay U r c k a h σ p∈fullVertices U r c := by
  rw [mem_smallVertexSet] at hp
  exact (mem_fullVertices U r c _).mpr ⟨contextDisplay_box U r c k a h σ p hp.1,
    contextDisplay_pattern U r c k a h σ p hp.2⟩

theorem contextDisplay_removeOne (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (i : PairCoords Bool a) :
    contextDisplay U r c k a h σ (removeOne p i) =
      removeOne (contextDisplay U r c k a h σ p) ((contextCoordinates U r c k a h).symm (.inr i)) := by
  funext w
  obtain ⟨z,rfl⟩ := (contextCoordinates U r c k a h).symm.surjective w
  cases z with
  | inl z => simp [contextDisplay,removeOne]
  | inr z => simp [contextDisplay,removeOne]

noncomputable def contextEdge (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1))
    (e : (Fin k → Fin (U+1)) × Sym2 (PairCoords Bool a → ℤ)) : Sym2 (SmallCoord U r c → ℤ) :=
  Sym2.map (contextDisplay U r c k a h e.1) e.2

theorem contextEdge_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) :
    Function.Injective (contextEdge U r c k a h) := by
  rintro ⟨σ,e⟩ ⟨τ,f⟩ he
  refine Sym2.inductionOn₂ e f (fun x y z w => ?_) he
  intro he
  change s(contextDisplay U r c k a h σ x,contextDisplay U r c k a h σ y)=
    s(contextDisplay U r c k a h τ z,contextDisplay U r c k a h τ w) at he
  rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · obtain ⟨rfl,rfl⟩ := contextDisplay_joint_inj U r c k a h σ τ x z hx
    obtain ⟨_,rfl⟩ := contextDisplay_joint_inj U r c k a h σ σ y w hy
    rfl
  · obtain ⟨rfl,rfl⟩ := contextDisplay_joint_inj U r c k a h σ τ x w hx
    obtain ⟨_,rfl⟩ := contextDisplay_joint_inj U r c k a h σ σ y z hy
    exact Prod.ext rfl Sym2.eq_swap

theorem contextEdge_mem (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (e : Sym2 (PairCoords Bool a → ℤ)) (he : e∈smallUnitEdges U a) :
    contextEdge U r c k a h (σ,e)∈fullUnitEdges U r c := by
  classical
  obtain ⟨hv,D,i,j,hij,rfl⟩ := Finset.mem_filter.mp he
  rw [Finset.mk_mem_sym2_iff] at hv
  apply Finset.mem_filter.mpr
  constructor
  · change s(contextDisplay U r c k a h σ (removeOne D i),
        contextDisplay U r c k a h σ (removeOne D j)) ∈ (fullVertices U r c).sym2
    exact Finset.mk_mem_sym2_iff.mpr ⟨contextDisplay_vertex U r c k a h σ _ hv.1,
      contextDisplay_vertex U r c k a h σ _ hv.2⟩
  · refine ⟨contextDisplay U r c k a h σ D,
      (contextCoordinates U r c k a h).symm (.inr i),
      (contextCoordinates U r c k a h).symm (.inr j),?_,?_⟩
    · intro he
      exact hij (Sum.inr.inj ((contextCoordinates U r c k a h).symm.injective he))
    · change s(contextDisplay U r c k a h σ (removeOne D i),
        contextDisplay U r c k a h σ (removeOne D j)) = _
      rw [contextDisplay_removeOne,contextDisplay_removeOne]

@[simp] theorem contextEdge_energy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (H : State m n → ℝ) (e : Sym2 (PairCoords Bool a → ℤ)) :
    edgeEnergy (smallKernel 0 U L C r c) (H ∘ coordinatesState U r c)
      (contextEdge U r c k a h (σ,e)) =
    edgeEnergy (contextKernel 0 U L C r c k a h σ)
      (H ∘ contextState U r c k a h σ) e := by
  induction e using Sym2.ind with
  | _ x y => rfl

noncomputable def fullUnitEnergy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : ℝ :=
  ∑ e ∈ fullUnitEdges U r c, edgeEnergy (smallKernel 0 U L C r c) (H ∘ coordinatesState U r c) e

theorem fullUnitEnergy_nonneg (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : 0 ≤ fullUnitEnergy U L C r c H :=
  Finset.sum_nonneg fun e _ => edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c) e

 

theorem contextEnergy_sum_le (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (H : State m n → ℝ) :
    (∑ σ : Fin k → Fin (U+1), contextEnergy U L C r c k a h σ H) ≤ fullUnitEnergy U L C r c H := by
  classical
  let E := edgeEnergy (smallKernel 0 U L C r c) (H ∘ coordinatesState U r c)
  have hh : (∑ σ : Fin k → Fin (U+1), contextEnergy U L C r c k a h σ H) =
      ∑ q ∈ Finset.univ ×ˢ smallUnitEdges U a, E (contextEdge U r c k a h q) := by
    rw [Finset.sum_product]
    simp only [E,contextEdge_energy,contextEnergy]
  rw [hh]
  rw [← Finset.sum_image (fun x _ y _ he => contextEdge_injective U r c k a h he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨⟨σ,e⟩,hq,rfl⟩ := Finset.mem_image.mp he
    exact contextEdge_mem U r c k a h σ e (Finset.mem_product.mp hq).2
  · intro e he hne
    exact edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c) e

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

theorem sum_snoc (U k : ℕ) (F : (Fin (k+1) → Fin (U+1)) → ℝ) :
    (∑ σ : Fin k → Fin (U+1), ∑ j : Fin (U+1), F (Fin.snoc σ j)) = ∑ τ, F τ := by
  rw [Finset.sum_comm]
  have he := Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k+1) => Fin (U+1))) F
  rw [Fintype.sum_prod_type] at he
  exact he

 

theorem contextTree_level_sum_le (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) (l a k : ℕ) (h : Fintype.card (SmallSlot U r c)=k+a) (hl : l<a) :
    (∑ σ : Fin k → Fin (U+1), exposureLevel U a (contextTree U L C r c H a k h σ) l) ≤
      fullUnitEnergy U L C r c H := by
  induction l generalizing a k with
  | zero =>
    cases a with
    | zero => omega
    | succ a => exact contextEnergy_sum_le U L C r c k a h H
  | succ l ih =>
    cases a with
    | zero => omega
    | succ a =>
      simp only [contextTree,exposureLevel]
      have h' : Fintype.card (SmallSlot U r c) = (k+1)+a := by omega
      change (∑ σ : Fin k → Fin (U+1), ∑ j : Fin (U+1),
        exposureLevel U a (contextTree U L C r c H a (k+1) h' (Fin.snoc σ j)) l) ≤ _
      rw [sum_snoc U k (fun τ => exposureLevel U a
        (contextTree U L C r c H a (k+1) h' τ) l)]
      exact ih a (k+1) h' (by omega)

theorem root_level_le (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) (l : ℕ) (hl : l<Fintype.card (SmallSlot U r c)) :
    exposureLevel U (Fintype.card (SmallSlot U r c))
      (contextTree U L C r c H (Fintype.card (SmallSlot U r c)) 0 (by omega) Fin.elim0) l ≤
      fullUnitEnergy U L C r c H := by
  have hh := contextTree_level_sum_le U L C r c H l (Fintype.card (SmallSlot U r c)) 0 (by omega) hl
  simp only [Fintype.sum_unique] at hh
  convert hh using 1
  congr 2

 

theorem concrete_transversal_variance (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hU : 2 ≤ U) (hC2 : 2 ≤ C) (hd : 1 ≤ d) (hslots : Fintype.card (SmallSlot U r c) ≤ d)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) :
    weightedVariance
      (fun τ => (weight U L r c (profileState U r c 0 (Fintype.card (SmallSlot U r c))
        (by omega) Fin.elim0 τ):ℝ))
      (fun τ => H (profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0 τ)) ≤
      4*(d:ℝ)^2*((U:ℝ)+1)^6 * fullUnitEnergy U L C r c H := by
  have hb := exposure_variance_level_bound U (4*(d:ℝ)*((U:ℝ)+1)^6) (by positivity)
    (Fintype.card (SmallSlot U r c))
    (fun τ => (weight U L r c (profileState U r c 0 (Fintype.card (SmallSlot U r c))
      (by omega) Fin.elim0 τ):ℝ))
    (fun τ => H (profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0 τ))
    (fun τ => by positivity) _
    (contextTree_childBounds U L C d r c hU hC2 hd hslots hrc hC H _ 0 (by omega) Fin.elim0)
    (fullUnitEnergy U L C r c H) (root_level_le U L C r c H)
  refine hb.trans ?_
  have hs : (Fintype.card (SmallSlot U r c):ℝ) ≤ d := by exact_mod_cast hslots
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ (4*(d:ℝ)*((U:ℝ)+1)^6)*fullUnitEnergy U L C r c H from
      mul_nonneg (by positivity) (fullUnitEnergy_nonneg U L C r c H))
  nlinarith only [hm]

end Contingency.PaddedGraph

end

end OAI
