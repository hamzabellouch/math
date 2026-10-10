import OAI.MeasureTheory.Falconer.Incidence.LoomisWhitneyThree

namespace OAI

/-! # The three-coordinate count for finite subsets of infinite grids -/

namespace Falconer
variable {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem finite_loomis_whitney_three_arbitrary (S : Finset (X × Y × Z)) :
    (S.card : ℝ)^2 ≤
      ((S.image (fun p => (p.1,p.2.1))).card : ℝ)*
      ((S.image (fun p => (p.2.1,p.2.2))).card : ℝ)*
      ((S.image (fun p => (p.2.2,p.1))).card : ℝ) := by
  classical
  let A := S.image (fun p => p.1)
  let B := S.image (fun p => p.2.1)
  let C := S.image (fun p => p.2.2)
  let lift : {p // p ∈ S} → A × B × C := fun p =>
    (⟨p.val.1,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩,
      ⟨p.val.2.1,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩,
      ⟨p.val.2.2,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩)
  let T := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z : A × B × C => (z.1.val,z.2.1.val,z.2.2.val)) he
  have hc : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hxy : (T.image (fun p => (p.1,p.2.1))).card =
      (S.image (fun p => (p.1,p.2.1))).card := by
    let f : A × B → X × Y := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.1,p.val.2.1)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.1,p.2.1)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.1,p.2.1))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hyz : (T.image (fun p => (p.2.1,p.2.2))).card =
      (S.image (fun p => (p.2.1,p.2.2))).card := by
    let f : B × C → Y × Z := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.2.1,p.val.2.2)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.2.1,p.2.2)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.2.1,p.2.2))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hzx : (T.image (fun p => (p.2.2,p.1))).card =
      (S.image (fun p => (p.2.2,p.1))).card := by
    let f : C × A → Z × X := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.2.2,p.val.1)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.2.2,p.1)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.2.2,p.1))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hh := finite_loomis_whitney_three T
  rw [hc,hxy,hyz,hzx] at hh
  exact hh

end Falconer

end OAI
