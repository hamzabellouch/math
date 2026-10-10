import OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def varyingAssignedGate {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : Prop :=
  (∀ i hi,x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))∈L₁ (eraseSecondSlots x) i) ∧
  (∀ i hi,x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))∈L₂ (eraseSecondSlots x) i)

omit [DecidableEq ι] in
lemma varyingAssignedGate_attach {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i∈J₁,ι)×(∀ i∈J₂,ι)) :
    varyingAssignedGate J₁ J₂ L₁ L₂ (attachPairedSlots J₁ J₂ (x,q)) ↔
      q.1∈J₁.pi (L₁ x) ∧ q.2∈J₂.pi (L₂ x) := by
  simp only [varyingAssignedGate,attachPairedSlots,erase_attachSecondSlots]
  simp only [attachSecondSlots,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,Finset.mem_pi]

def varyingAssignedSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :=
  (assignedSecondSource source J₁ J₂ base₁ base₂).filter (varyingAssignedGate J₁ J₂ L₁ L₂)

theorem varyingAssignedSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S⊆T)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :
    varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂⊆
      varyingAssignedSource T J₁ J₂ base₁ base₂ L₁ L₂ := by
  exact Finset.filter_subset_filter _ (assignedSecondSource_mono hST J₁ J₂ base₁ base₂)

theorem varyingAssignedSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card)→ℂ) :
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,F x =
      ∑ y∈source,∑ q∈(J₁.pi (fun i=>L₁ y i∩(y.second.sourceCommon∪y.second.overlap)))×ˢ
        (J₂.pi (fun i=>L₂ y i∩(y.second.sourceCommon∪y.second.overlap))),F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [varyingAssignedSource,Finset.sum_filter,assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_product,varyingAssignedGate_attach,Finset.mem_pi,Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨fun i hi=>⟨h₃ i hi,(h₁ i hi).2⟩,fun i hi=>⟨h₄ i hi,(h₂ i hi).2⟩⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨⟨fun i hi=>⟨hL₁ y hy i hi (h₁ i hi).1,(h₁ i hi).2⟩,
      fun i hi=>⟨hL₂ y hy i hi (h₂ i hi).1,(h₂ i hi).2⟩⟩,
      fun i hi=>(h₁ i hi).1,fun i hi=>(h₂ i hi).1⟩

theorem varyingAssignedSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ) (w P : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈source,w y*(star (primeMark J₁ (L₁ y) a₁ (y.second.sourceCommon∪y.second.overlap))*
      primeMark J₂ (L₂ y) a₂ (y.second.sourceCommon∪y.second.overlap))*P y) =
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x)*P (eraseSecondSlots x) := by
  rw [varyingAssignedSource_sum source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_varying_lists_weighted_count
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {Jo : ℕ} (u v : Oˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈base₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈base₂ i,‖a₂ i q‖≤1)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hchild : ∀ x∈source,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows)
    (K : ℕ) (ho : Jo≤2*K) (hJ₁ : J₁.card≤K) (hJ₂ : J₂.card≤K)
    (w : MarkedSecondSource ι Jo 0→ℂ) (hw : ∀ x∈source,‖w x‖≤1) (F G : SecondChild→ℂ) :
    ‖∑ x∈source,w x*(star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap))*
      primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap))*
      F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x))‖ ≤
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ)*
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) := by
  let S := varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂
  have hsub : S⊆assignedSecondSource source J₁ J₂ base₁ base₂ := Finset.filter_subset _ _
  have hs' : ActualSecondSourceConditions p S :=
    (assignedSecondSource_conditions p source hs J₁ J₂ base₁ base₂).mono p hsub
  have herase : ∀ x∈S,eraseSecondSlots x∈source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ base₁ base₂ x).mp (hsub hx)
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card)=>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hw' : ∀ x∈S,‖w' x‖≤1 := by
    intro x hx
    rw [show w' x=w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ base₁ base₂ a₁ a₂ ha₁ ha₂ x (hsub hx))
  have hc' : ∀ x∈S,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := varyingAssignedSource_sum_marks source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂ a₁ a₂ w
    (fun x=>F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end SevenEighths.InverseMoment

end

end OAI
