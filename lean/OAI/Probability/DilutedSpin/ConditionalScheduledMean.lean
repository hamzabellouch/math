import OAI.Probability.DilutedSpin.ScheduledEvaluationContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The scheduled conditional mean on a literal full path, evaluated after
`e` transitions. Before the first branching this is the usual conditional
expectation; no independently sampled prefix occurs in this definition. -/
noncomputable def conditionalScheduledMean : (H d e : ℕ) →
    (S : ReducedTopology) → (S.Vertex → ℕ) → KernelTower Ω H →
    (FinitePath Ω H → ℝ) → FinitePath Ω H → ℝ
  | 0,_,_,_,_,T,f,_ => PrescribedTree.treeMean .leaf T f
  | H+1,d,0,S,q,T,f,_ => PrescribedTree.treeMean (realize (H+1) d S q) T f
  | H+1,d,e+1,S,q,T,f,x => conditionalScheduledMean H (d+1) e S q (T.2 x.1)
      (fun y => f (x.1,y)) x.2

lemma conditionalScheduledMean_zero (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (x : FinitePath Ω H) :
    conditionalScheduledMean H d 0 S q T f x=PrescribedTree.treeMean (realize H d S q) T f := by
  cases H <;> rfl

lemma conditionalScheduledMean_bound (H d e : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x|≤1) (x : FinitePath Ω H) :
    |conditionalScheduledMean H d e S q T f x|≤1 := by
  induction H generalizing d e with
  | zero => exact PrescribedTree.treeMean_bound .leaf T hf
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.treeMean_bound _ T hf
    | succ e => exact ih (d+1) e (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

/-- Exact agreement with the fixed-terminal-reserve evaluation martingale. -/
lemma conditionalScheduledMean_eq_prefix (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (x : FinitePath Ω (n+r)) :
    conditionalScheduledMean (n+r) d e.val S q T f x=scheduledPrefixMean n r d e S q T f x := by
  induction r generalizing d with
  | zero =>
    have he : e=0 := Fin.eq_zero e
    subst e
    exact conditionalScheduledMean_zero n d S q T f x
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact conditionalScheduledMean_zero (n+(r+1)) d S q T f x
    · exact ih (d+1) e (T.2 x.1) (fun y => f (x.1,y)) x.2

/-- Exact tail-projector geometry, with the original prefix retained. -/
lemma conditionalScheduledMean_eq_tail (H p d : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → ℝ)
    (x : FinitePath Ω (H+p)) :
    conditionalScheduledMean (H+p) d p S q T f x=
      PrescribedTree.tailMean (realize H (d+p) S q) p T f x := by
  induction p generalizing d with
  | zero => exact conditionalScheduledMean_zero H d S q T f x
  | succ p ih =>
    change conditionalScheduledMean (H+p) (d+1) p S q (T.2 x.1) (fun y => f (x.1,y)) x.2=_
    have h := ih (d+1) (T.2 x.1) (fun y => f (x.1,y)) x.2
    simpa only [PrescribedTree.tailMean,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Proper-child mean product at an actual evaluation prefix, expressed
without a choice of terminal reserve. -/
noncomputable def conditionalScheduledProduct {ι : Type*} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ)
    (x : FinitePath Ω H) (i : Fin N) : ℝ :=
  ∏ j, conditionalScheduledMean H d e (C j) (q j) T (fun y => f y i) x

lemma conditionalScheduledProduct_bound {ι : Type*} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (x : FinitePath Ω H) (i : Fin N) : |conditionalScheduledProduct H d e C q T f x i|≤1 := by
  unfold conditionalScheduledProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ =>
    conditionalScheduledMean_bound H d e (C j) (q j) T (fun y => f y i) (fun y => hf y i) x)

lemma conditionalScheduledProduct_eq_prefix {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    conditionalScheduledProduct (n+r) d e.val C q T f=scheduledProductMean n r d C q e T f := by
  funext x i
  unfold conditionalScheduledProduct scheduledProductMean
  exact Finset.prod_congr rfl (fun j _ => conditionalScheduledMean_eq_prefix n r d (C j) (q j) e T _ x)

/-- The simultaneous-schedule projector is literally this conditional
proper-child product. This is the bridge between the two continuity costs. -/
lemma conditionalScheduledProduct_eq_childSchedule {ι α : Type} [Fintype ι]
    {L : ℕ} [NeZero L] (H p : ℕ) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (s : (j : ι) → (C j).Vertex → Bool) (Q : α → Fin L)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) :
    conditionalScheduledProduct (H+p) 0 p C
      (fun j v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T f=
      childScheduleProjection H p p C e τ s T f Q := by
  funext x i
  unfold conditionalScheduledProduct childScheduleProjection scheduledTailProjection
  apply Finset.prod_congr rfl
  intro j _
  simpa only [Nat.zero_add] using conditionalScheduledMean_eq_tail H p 0 (C j)
    (fun v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T (fun y => f y i) x

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance conditionalScheduledMeanDepthDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- Put a distinguished evaluation coordinate back into its full parent
cube, keeping every other branching coordinate literally unchanged. -/
def insertCoordinate (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L) : α → Fin L :=
  (Equiv.piSplitAt a (fun _ : α => Fin L)).symm (t,rest)

omit [Fintype α] [NeZero L] in
@[simp] lemma insertCoordinate_self (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L) :
    insertCoordinate a t rest a=t := by simp [insertCoordinate,Equiv.piSplitAt_symm_apply]

omit [Fintype α] [NeZero L] in
@[simp] lemma insertCoordinate_other (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L)
    (j : {j : α // j≠a}) : insertCoordinate a t rest j=rest j := by
  simp [insertCoordinate,Equiv.piSplitAt_symm_apply,j.property]

 
lemma average_split (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
      average (fun rest => D (insertCoordinate a t rest)) (fun rest => F (insertCoordinate a t rest))) := by
  unfold average depthLaw insertCoordinate
  exact FiniteLaw.expect_pi_split _ a _

/-- Fix all child coordinates first, then average the evaluation coordinate. -/
lemma average_split_comm (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(depthLaw {j : α // j≠a} L).expect (fun rest =>
      (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
        if D (insertCoordinate a t rest) then F (insertCoordinate a t rest) else 0)) := by
  rw [average_split a D F]
  exact FiniteLaw.expect_comm _ _ _

/-- Uniform fixed-evaluation estimates survive the unused evaluation
coordinate with no extra L factor. -/
lemma average_of_slice_le (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ)
    (h : ∀ t : Fin L, average (fun rest => D (insertCoordinate a t rest))
      (fun rest => F (insertCoordinate a t rest))≤c) : average D F≤c := by
  rw [average_split a D F]
  exact ((FiniteLaw.uniform : FiniteLaw (Fin L)).expect_mono h).trans_eq
    (FiniteLaw.expect_const _ _)

omit [NeZero L] in
/-- Sum of a literal zero-extended prefix family. -/
lemma sum_zeroExtension {r : ℕ} (hr : r≤L) (F : Fin r → ℝ) :
    (∑ t : Fin L, if h : t.val<r then F ⟨t.val,h⟩ else 0)=∑ e : Fin r, F e := by
  classical
  let E : {t : Fin L // t.val<r} ≃ Fin r :=
    { toFun := fun t => ⟨t.1.val,t.2⟩
      invFun := fun t => ⟨⟨t.val,lt_of_lt_of_le t.isLt hr⟩,t.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ t : {t : Fin L // t.val<r}, F ⟨t.1.val,t.2⟩ := by
      rw [Finset.sum_dite]
      simp only [Finset.sum_const_zero,add_zero]
      exact (Equiv.subtypeEquivRight (by simp)).sum_comp
        (fun t : {t : Fin L // t.val<r} => F ⟨t.1.val,t.2⟩)
    _ = _ := Equiv.sum_comp E F

lemma uniform_zeroExtension {r : ℕ} (hr : r≤L) (F : Fin r → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect
      (fun t => if h : t.val<r then F ⟨t.val,h⟩ else 0)=(∑ e : Fin r, F e)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  rw [← Finset.mul_sum,show Fintype.card (Fin L)=L from Fintype.card_fin L,sum_zeroExtension hr F]
  exact (div_eq_inv_mul _ _).symm

end DilutedSpinGlass.DepthAverage
end

end

end OAI
