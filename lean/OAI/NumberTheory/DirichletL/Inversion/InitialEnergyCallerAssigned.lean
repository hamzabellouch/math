import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCaller
import OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum

namespace OAI

noncomputable section

open scoped BigOperators Classical
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAssigned
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) : Source (ι:=ι) J where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := q

def erase {J : ℕ} (x : Source (ι:=ι) J) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) :
    erase (attach x q) = x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

omit [DecidableEq ι] in
theorem attach_injective {J : ℕ} :
    Function.Injective (fun z : Source (ι:=ι) 0 × (Fin J→ι) => attach z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [erase_attach] using congrArg erase h
  · exact congrArg Source.assigned h

def attachPair (J₁ J₂ : Finset σ)
    (z : Source (ι:=ι) 0 × ((∀ i∈J₁,ι) × (∀ i∈J₂,ι))) :
    Source (ι:=ι) (J₁.card+J₂.card) :=
  attach z.1 (pairedSlotAssignment J₁ J₂ z.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPair_injective (J₁ J₂ : Finset σ) :
    Function.Injective (attachPair (ι:=ι) J₁ J₂) := by
  intro x y h
  have he := @attach_injective ι (J₁.card + J₂.card)
    (x.1,pairedSlotAssignment J₁ J₂ x.2) (y.1,pairedSlotAssignment J₁ J₂ y.2) h
  exact Prod.ext (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.2) he))

def assignedSource (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : Finset (Source (ι:=ι) (J₁.card+J₂.card)) :=
  ((S ×ˢ ((J₁.pi L₁) ×ˢ (J₂.pi L₂))).filter
    (fun z=>∀ i,pairedSlotAssignment J₁ J₂ z.2 i∈z.1.common∪z.1.overlap)).image
      (attachPair J₁ J₂)

def coefficient (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi=>x.assigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi=>x.assigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem coefficient_attach (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) 0) (q : (∀ i∈J₁,ι) × (∀ i∈J₂,ι)) :
    coefficient J₁ J₂ a₁ a₂ (attachPair J₁ J₂ (x,q)) = pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [coefficient,attachPair,attach,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem assignedSource_sum (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) (F : Source (ι:=ι) (J₁.card+J₂.card)→ℂ) :
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,F x =
      ∑ y∈S,∑ q∈(J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap))),F (attachPair J₁ J₂ (y,q)) := by
  rw [assignedSource,Finset.sum_image (fun x _ y _ he=>attachPair_injective J₁ J₂ he),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem original_marks_eq_assigned (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (w P : Source (ι:=ι) 0→ℂ) :
    (∑ y∈S,w y*(star (primeMark J₁ L₁ a₁ (y.common∪y.overlap))*
      primeMark J₂ L₂ a₂ (y.common∪y.overlap))*P y) =
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,
      (w (erase x)*coefficient J₁ J₂ a₁ a₂ x)*P (erase x) := by
  rw [assignedSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficient_attach]
  simp only [attachPair,erase_attach]

theorem assignedSource_support (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    erase x∈S ∧ x.divisor⊆x.common ∧ ∀ i,x.assigned i∈x.common∪x.overlap := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hyS := (Finset.mem_product.mp hmem).1
  exact ⟨by simpa only [attachPair,erase_attach] using hyS,hdiv y hyS,hq⟩

theorem coefficient_norm_le_one (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈L₂ i,‖a₂ i q‖≤1)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    ‖coefficient J₁ J₂ a₁ a₂ x‖≤1 := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hq' : q∈(J₁.pi L₁ ×ˢ J₂.pi L₂).filter
      (fun q=>∀ i,pairedSlotAssignment J₁ J₂ q i∈y.common∪y.overlap) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).2,hq⟩
  rw [paired_assignment_filter] at hq'
  rw [coefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ q hq' ha₁ ha₂

theorem assigned_tuple_valid
    (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common) (u : ActualEisensteinCubic.Oˣ)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    InitialSourceValid (toTuple p (sectorSource u x)) := by
  obtain ⟨_,hdivx,hassigned⟩ := assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
    ((u:ActualEisensteinCubic.O)^5*x.frequency) x.assigned hdivx hassigned

end SevenEighths.InverseInitialEnergyCallerAssigned

end

end OAI
