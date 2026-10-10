import Mathlib
import OAI.Probability.BinarySweep.Trajectories.EndpointEvents
import OAI.Probability.BinarySweep.FiniteLaws.OneCard

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
lemma localEndpointMass_empty_line (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (j : Fin b) (y : GridOutside bits j)
    (hh : ∀k, (fun i : {i : Fin b // i≠j} => H.position j.castSucc k i) ≠ y)
    (ha : ∀i ∈ A, endpointLine (e i) j≠y) :
    localEndpointMass H z A e j y=1 := by
  unfold localEndpointMass
  simp only [assigns_empty_line H j y hh,localEndpointEvent_empty_line A e j y ha,
    and_self,ite_true,lineLaw_sum]

lemma localEndpointMass_insert_at (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I) (j : Fin b)
    (hh : ∀k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    localEndpointMass H z (insert i A) e j (endpointLine (e i) j)=
      (Fintype.card (Slot (bits j)):ℝ)⁻¹ := by
  unfold localEndpointMass
  simp only [assigns_empty_line H j _ hh,localEndpointEvent_insert,
    localEndpointEvent_empty_line A e j _ ha,true_and,and_true,
    forall_true_left]
  exact line_one_card_ite (bits j) z ((e i).1 j) ((e i).2 j)

lemma localEndpointMass_insert_other (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I) (j : Fin b) (y : GridOutside bits j)
    (hy : y≠endpointLine (e i) j) :
    localEndpointMass H z (insert i A) e j y=localEndpointMass H z A e j y := by
  unfold localEndpointMass
  apply Finset.sum_congr rfl
  intro σ _
  simp only [localEndpointEvent_insert,Ne.symm hy,IsEmpty.forall_iff,true_and]

lemma prod_one_coordinate {J : Type*} [Fintype J] [DecidableEq J]
    (f g : J → ℝ) (j : J) (a : ℝ) (hf : f j=1) (hg : g j=a)
    (he : ∀k, k≠j → g k=f k) : ∏k, g k=a*∏k, f k := by
  calc
    _ = ∏k, (if k=j then a else 1)*f k := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k=j
      · subst k; simp [hf,hg]
      · simp [hk,he k hk]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

variable [Fintype I]

lemma endpointMass_insert_isolated (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j, ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    endpointMass H z (insert i A) e=(gridSize bits:ℝ)⁻¹ * endpointMass H z A e := by
  rw [endpointMass_factor,endpointMass_factor]
  have hj (j : Fin b) : (∏y, localEndpointMass H z (insert i A) e j y) =
      (Fintype.card (Slot (bits j)):ℝ)⁻¹ * ∏y, localEndpointMass H z A e j y := by
    exact prod_one_coordinate _ _ (endpointLine (e i) j) _
      (localEndpointMass_empty_line H z A e j _ (hh j) (ha j))
      (localEndpointMass_insert_at H z A e i j (hh j) (ha j))
      (fun y hy => localEndpointMass_insert_other H z A e i j y hy)
  simp only [hj,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  congr 2
  simp only [Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,
    gridSize,Nat.cast_prod]

def endpointProbability (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) : ℝ := endpointMass H z A e / conditionalNormalizer H z

lemma endpointProbability_insert_isolated (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j, ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    endpointProbability H z (insert i A) e=(gridSize bits:ℝ)⁻¹ * endpointProbability H z A e := by
  unfold endpointProbability
  rw [endpointMass_insert_isolated H z A e i hh ha,mul_div_assoc]

end BinaryCoordinateSweeps

end

end OAI
