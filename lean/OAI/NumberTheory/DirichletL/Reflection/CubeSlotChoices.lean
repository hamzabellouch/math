import OAI.NumberTheory.DirichletL.Reflection.CubeSlots

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 def cubeDivList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => P∣H)
 def cubeAwayList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => ¬P∣H)
 def cubeChoiceActive (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (p : ∀ i,L i) : Finset σ :=
  Finset.univ.filter (fun i => ¬(p i).val∣H)

abbrev CubeSlotChoices (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :=
  Σ T : Finset σ,(∀ i : {i // i∉T},cubeDivList H (L i.val))×(∀ i : T,cubeAwayList H (L i.val))

def cubeChoicesJoin (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) : ∀ i,L i :=
  (slotChoiceSplit L x.1).symm
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩,
     fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)

lemma cubeChoicesJoin_label (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) :
    cubeChoiceActive H L (cubeChoicesJoin H L x)=x.1 := by
  rcases x with ⟨T,b,a⟩
  ext i
  simp only [cubeChoiceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i∈T
  · have ha := (Finset.mem_filter.mp (a ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_active L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_true ha hi
  · have hb := (Finset.mem_filter.mp (b ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_inactive L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_false (not_not_intro hb) hi

lemma cubeChoicesJoin_injective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Injective (cubeChoicesJoin H L) := by
  rintro ⟨T,b,a⟩ ⟨U,d,c⟩ he
  have ht := congrArg (cubeChoiceActive H L) he
  rw [cubeChoicesJoin_label,cubeChoicesJoin_label] at ht
  dsimp only at ht
  subst U
  apply congrArg (fun q => (⟨T,q⟩ : CubeSlotChoices H L))
  have hx := congrArg (slotChoiceSplit L T) he
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply] at hx
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.2 i).val) hx
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.1 i).val) hx

lemma cubeChoicesJoin_surjective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Surjective (cubeChoicesJoin H L) := by
  intro p
  let T := cubeChoiceActive H L p
  let a : ∀ i : T,cubeAwayList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,(Finset.mem_filter.mp i.property).2⟩⟩
  have hd (i : {i // i∉T}) : (p i.val).val∣H := by
    by_contra hi
    exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  let b : ∀ i : {i // i∉T},cubeDivList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,hd i⟩⟩
  refine ⟨⟨T,b,a⟩,?_⟩
  apply (slotChoiceSplit L T).injective
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply]
  apply Prod.ext <;> funext i <;> apply Subtype.ext <;> rfl

def cubeSlotChoiceEquiv (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    CubeSlotChoices H L ≃ (∀ i,L i) :=
  Equiv.ofBijective (cubeChoicesJoin H L) ⟨cubeChoicesJoin_injective H L,cubeChoicesJoin_surjective H L⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
