import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype
variable {α : Type*} [DecidableEq α]
def inverseOrientation (r : Fin 8) : Fin 8 :=
  if r = 3 then 5 else if r = 5 then 3 else r
theorem orient_inverse_left (r : Fin 8) (p : Cell) :
    orient (inverseOrientation r) (orient r p) = p := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> simp [orient, inverseOrientation]
theorem orient_inverse_right (r : Fin 8) (p : Cell) :
    orient r (orient (inverseOrientation r) p) = p := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> simp [orient, inverseOrientation]
def orientationEquiv (r : Fin 8) : Cell ≃ Cell where
  toFun := orient r
  invFun := orient (inverseOrientation r)
  left_inv := orient_inverse_left r
  right_inv := orient_inverse_right r
def translationEquiv (t : Cell) : Cell ≃ Cell where
  toFun := fun p => p + t
  invFun := fun p => p - t
  left_inv := fun p => add_sub_cancel_right p t
  right_inv := fun p => sub_add_cancel p t
def placementEquiv (r : Fin 8) (t : Cell) : Cell ≃ Cell :=
  (orientationEquiv r).trans (translationEquiv t)
@[simp] theorem placementEquiv_apply (r : Fin 8) (t p : Cell) :
    placementEquiv r t p = placement r t p := rfl
@[simp] theorem coe_placementEquiv (r : Fin 8) (t : Cell) :
    (placementEquiv r t : Cell → Cell) = placement r t := rfl
def composeOrientation (r s : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6],
    ![2,5,0,7,6,1,4,3], ![3,4,1,6,7,0,5,2],
    ![4,3,6,1,0,7,2,5], ![5,2,7,0,1,6,3,4],
    ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] r s
theorem orient_comp (r s : Fin 8) (p : Cell) :
    orient r (orient s p) = orient (composeOrientation r s) p := by
  fin_cases r <;> fin_cases s <;> rcases p with ⟨x, y⟩ <;>
    simp [orient, composeOrientation]
theorem orient_add (r : Fin 8) (p q : Cell) :
    orient r (p + q) = orient r p + orient r q := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> rcases q with ⟨u, v⟩ <;>
    simp [orient, add_comm]
theorem placement_comp (r s : Fin 8) (t u p : Cell) :
    placement r t (placement s u p) =
      placement (composeOrientation r s) (orient r u + t) p := by
  simp only [placement, orient_add, orient_comp, add_assoc]
theorem HasSnaky.mono {M N : Finset Cell} (h : HasSnaky M) (hMN : M ⊆ N) :
    HasSnaky N := by
  obtain ⟨r, t, hrt⟩ := h
  exact ⟨r, t, hrt.trans hMN⟩
theorem HasSnaky.placed (r : Fin 8) (t : Cell) (M : Finset Cell)
    (h : HasSnaky M) : HasSnaky (M.image (placement r t)) := by
  obtain ⟨s, u, hsu⟩ := h
  refine ⟨composeOrientation r s, orient r u + t, ?_⟩
  intro z hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨placement s u p,
    hsu (Finset.mem_image_of_mem (placement s u) hp), ?_⟩
  exact (placement_comp r s t u p).trans hpz
theorem placed_template {n : ℕ} {A H : Finset Cell}
    (h : Template HasSnaky n A H) (r : Fin 8) (t : Cell) :
    Template HasSnaky n (A.image (placement r t)) (H.image (placement r t)) := by
  have hw : ∀ X, HasSnaky X → HasSnaky (X.image (placementEquiv r t)) := by
    intro X hx
    simpa only [coe_placementEquiv] using HasSnaky.placed r t X hx
  simpa only [coe_placementEquiv] using h.transport (placementEquiv r t) hw
def basePoint (i : Fin 6) : Cell := ![(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)] i
def baseEnvelope (i : Fin 6) : Finset Cell :=
  snaky.image (placement 0 (-basePoint i))
def baseRequired (i : Fin 6) : Finset Cell := (baseEnvelope i).erase (0, 0)
theorem basePoint_mem (i : Fin 6) : basePoint i ∈ snaky := by
  fin_cases i <;> decide
theorem base_works (i : Fin 6) :
    Template HasSnaky 1 (baseRequired i) (baseEnvelope i) := by
  apply immediate_template HasSnaky (baseEnvelope i) (0, 0)
  · exact Finset.mem_image.mpr ⟨basePoint i, basePoint_mem i, by simp [placement, orient]; rfl⟩
  · intro M hM
    exact ⟨0, -basePoint i, hM⟩
end SnakyPrototype

end OAI
