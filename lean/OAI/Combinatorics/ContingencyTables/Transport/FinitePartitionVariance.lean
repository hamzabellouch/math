import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance

namespace OAI

/-! # Exact variance decomposition for finite physical prefix partitions -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X C D : Type*} [Fintype X] [Fintype C] [Fintype D]

noncomputable def fibreWeight (w : X → ℝ) (π : X → C) (c : C) : X → ℝ :=
  fun x => if π x=c then w x else 0

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_mul (w H : X → ℝ) (π : X → C) (c : C) (x : X) :
    fibreWeight (fun x => w x*H x) π c x=fibreWeight w π c x*H x := by
  simp only [fibreWeight,ite_mul,zero_mul]

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_nonnegative (w : X → ℝ) (hw : ∀ x,0 ≤ w x) (π : X → C) (c : C) :
    ∀ x,0 ≤ fibreWeight w π c x := by
  intro x
  unfold fibreWeight
  split_ifs
  · exact hw x
  · exact le_rfl

omit [Fintype D] in
theorem variance_partition (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (π : X → C) :
    variance w H=(∑ c,variance (fibreWeight w π c) H)+
      variance (fun c => ∑ x,fibreWeight w π c x)
        (fun c => mean (fibreWeight w π c) H) := by
  have hw' : ∀ c x,0 ≤ fibreWeight w π c x := fibreWeight_nonnegative w hw π
  have hsplit := variance_split (fibreWeight w π) (fun _ => H) hw'
  have he : variance (fun p : X×C => fibreWeight w π p.2 p.1) (fun p => H p.1)=variance w H := by
    rw [variance_formula (fun p : X×C => fibreWeight w π p.2 p.1)
      (fun p => H p.1) (fun p => hw' p.2 p.1),variance_formula w H hw]
    simp only [Fintype.sum_prod_type,fibreWeight,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [he] at hsplit
  exact hsplit

noncomputable def partitionVariance (w H : X → ℝ) (π : X → C) : ℝ :=
  ∑ c,variance (fibreWeight w π c) H

noncomputable def partitionContribution (w H : X → ℝ) (π : X → C) (ρ : X → D) : ℝ :=
  ∑ c,variance (fun d => ∑ x,fibreWeight (fibreWeight w π c) ρ d x)
    (fun d => mean (fibreWeight (fibreWeight w π c) ρ d) H)

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_pair (w : X → ℝ) (π : X → C) (ρ : X → D) (c : C) (d : D) :
    fibreWeight (fibreWeight w π c) ρ d=fibreWeight w (fun x => (π x,ρ x)) (c,d) := by
  funext x
  unfold fibreWeight
  simp only [Prod.mk.injEq]
  by_cases hc : π x=c <;> by_cases hd : ρ x=d <;> simp only [hc,hd,↓reduceIte,and_self,
    false_and,and_false]

/-- Refining a physical prefix adds exactly its between-child variance.
All zero fibres are retained and contribute zero. -/
theorem partition_refinement (w H : X → ℝ) (hw : ∀ x,0 ≤ w x)
    (π : X → C) (ρ : X → D) :
    partitionVariance w H π=partitionVariance w H (fun x => (π x,ρ x))+
      partitionContribution w H π ρ := by
  have h (c : C) := variance_partition (fibreWeight w π c) H
    (fibreWeight_nonnegative w hw π c) ρ
  unfold partitionVariance partitionContribution
  simp_rw [h]
  rw [Finset.sum_add_distrib,Fintype.sum_prod_type]
  simp_rw [fibreWeight_pair]

omit [Fintype D] in
lemma partitionVariance_reindex {E : Type*} [Fintype E] (e : C ≃ E)
    (w H : X → ℝ) (π : X → C) :
    partitionVariance w H (fun x => e (π x))=partitionVariance w H π := by
  unfold partitionVariance
  symm
  apply Fintype.sum_equiv e
  intro c
  congr 1
  funext x
  simp only [fibreWeight,Equiv.apply_eq_iff_eq]

omit [Fintype C] [Fintype D] in
lemma variance_singleton_fibre (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (a : X) :
    variance (fibreWeight w id a) H=0 := by
  rw [variance_formula _ H (fibreWeight_nonnegative w hw id a)]
  simp only [fibreWeight,id_eq,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases hz : w a=0
  · simp only [hz,zero_mul,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,sub_zero]
  · field_simp
    ring

omit [Fintype C] [Fintype D] in
lemma partitionVariance_identity (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) :
    partitionVariance w H id=0 := by
  unfold partitionVariance
  simp only [variance_singleton_fibre w H hw,Finset.sum_const_zero]

end ContingencyTables.FiniteExposureVariance

end OAI
