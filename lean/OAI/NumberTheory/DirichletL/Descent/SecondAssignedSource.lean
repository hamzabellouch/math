import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalSplit
import OAI.NumberTheory.DirichletL.Descent.SlotAssignments

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def pairedSlotAssignment (J₁ J₂ : Finset σ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : Fin (J₁.card+J₂.card) → ι :=
  Fin.addCases (indexedSlotAssignment J₁ q.1) (indexedSlotAssignment J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

def pairedSlotWeight (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁ q.1)*slotAssignmentWeight J₂ a₂ q.2

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

def attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0)
    (newAssigned : Fin Jn → ι) : MarkedSecondSource ι Jo Jn where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := newAssigned

omit [DecidableEq ι] in
theorem attachSecondSlots_injective {Jo Jn : ℕ} :
    Function.Injective (fun q : MarkedSecondSource ι Jo 0 × (Fin Jn → ι) => attachSecondSlots q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · apply MarkedSecondSource.ext
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.cube) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstCommon) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstDivisor) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.second) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.quotient) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.oldAssigned) h
    · funext i; exact Fin.elim0 i
  · exact congrArg MarkedSecondSource.newAssigned h

def attachPairedSlots {Jo : ℕ} (J₁ J₂ : Finset σ)
    (q : MarkedSecondSource ι Jo 0 × ((∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))) :
    MarkedSecondSource ι Jo (J₁.card+J₂.card) :=
  attachSecondSlots q.1 (pairedSlotAssignment J₁ J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPairedSlots_injective {Jo : ℕ} (J₁ J₂ : Finset σ) :
    Function.Injective (attachPairedSlots (ι:=ι) (Jo:=Jo) J₁ J₂) := by
  intro q r h
  have he := @attachSecondSlots_injective ι Jo (J₁.card+J₂.card)
    (q.1,pairedSlotAssignment J₁ J₂ q.2) (r.1,pairedSlotAssignment J₁ J₂ r.2) h
  exact Prod.ext (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.2) he))

def assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    Finset (MarkedSecondSource ι Jo (J₁.card+J₂.card)) :=
  ((source ×ˢ ((J₁.pi (fun i => L₁ i)) ×ˢ (J₂.pi (fun i => L₂ i)))).filter
    (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q.2 j ∈ q.1.second.sourceCommon∪q.1.second.overlap)).image
      (attachPairedSlots J₁ J₂)

theorem mem_assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) :
    x ∈ assignedSecondSource source J₁ J₂ L₁ L₂ ↔
      ∃ y ∈ source, ∃ q₁ ∈ J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap)),
      ∃ q₂ ∈ J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap)),
        attachPairedSlots J₁ J₂ (y,(q₁,q₂)) = x := by
  constructor
  · intro hx
    obtain ⟨⟨y,q₁,q₂⟩,hmem,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hy,hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine ⟨y,hy,q₁,Finset.mem_pi.mpr ?_,q₂,Finset.mem_pi.mpr ?_,rfl⟩
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · rintro ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(y,(q₁,q₂)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,Finset.mem_product.mpr ⟨?_,?_⟩⟩,?_⟩,rfl⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q₁ hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q₂ hq₂ k)).2

theorem assignedSecondSource_conditions (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    ActualSecondSourceConditions p (assignedSecondSource source J₁ J₂ L₁ L₂) := by
  have hmem : ∀ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      ∃ y ∈ source, ∃ q, attachPairedSlots J₁ J₂ (y,q)=x ∧
        ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ y.second.sourceCommon∪y.second.overlap := by
    intro x hx
    obtain ⟨⟨y,q⟩,hmem,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨y,(Finset.mem_product.mp hmem).1,q,he,hq⟩
  constructor
  all_goals
    intro x hx
    obtain ⟨y,hy,q,rfl,hq⟩ := hmem x hx
  · exact hs.admissible y hy
  · exact hs.common_disjoint y hy
  · exact hs.first_divisor y hy
  · exact hs.second_divisor y hy
  · exact hs.old_support y hy
  · exact hq
  · exact hs.quotient_nonzero y hy

end
end SevenEighths.InverseMoment

end OAI
