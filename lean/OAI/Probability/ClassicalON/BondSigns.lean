import OAI.Probability.ClassicalON.BondLaw

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

def signFieldEquiv : Bool ≃ SignField where
  toFun b := if b then 0 else 1
  invFun a := a=0
  left_inv b := by cases b <;> decide
  right_inv a := by
    have ha : a=0 ∨ a=1 := by fin_cases a <;> [exact Or.inl rfl; exact Or.inr rfl]
    rcases ha with rfl | rfl <;> simp

@[simp] theorem signFieldEquiv_true : signFieldEquiv true=0 := rfl
@[simp] theorem signFieldEquiv_false : signFieldEquiv false=1 := rfl

def fieldSign (a : SignField) : ℝ := if a=0 then 1 else -1

theorem signField_cases (a : SignField) : a=0 ∨ a=1 := by
  fin_cases a <;> [exact Or.inl rfl; exact Or.inr rfl]

@[simp] theorem fieldSign_zero : fieldSign 0=1 := by simp [fieldSign]
@[simp] theorem fieldSign_one : fieldSign 1= -1 := by simp [fieldSign]

theorem fieldSign_add (a b : SignField) : fieldSign (a+b)=fieldSign a*fieldSign b := by
  have htwo : (1 : SignField)+1=0 := rfl
  rcases signField_cases a with rfl | rfl <;> rcases signField_cases b with rfl | rfl <;> simp [htwo]

theorem fieldSign_sq (a : SignField) : fieldSign a*fieldSign a=1 := by
  rcases signField_cases a with rfl | rfl <;> simp

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def compatibleSigns (left right : E → V) (η : E → Bool) : Set (V → Bool) :=
  {s | ∀ e,η e=true → s (left e)=s (right e)}

def compatibleSignsEquiv (left right : E → V) (η : E → Bool) :
    compatibleSigns left right η ≃ bondSubspace left right η :=
  (Equiv.piCongrRight (fun _ : V => signFieldEquiv)).subtypeEquiv (by
    intro s
    change (∀ e,η e=true → s (left e)=s (right e)) ↔
      ∀ e,η e=true → signFieldEquiv (s (left e))=signFieldEquiv (s (right e))
    simp only [Equiv.apply_eq_iff_eq])

omit [Fintype E] in
theorem compatibleSigns_card (left right : E → V) (η : E → Bool) :
    Fintype.card (compatibleSigns left right η)=2^bondRank left right η := by
  rw [Fintype.card_congr (compatibleSignsEquiv left right η),Module.card_eq_pow_finrank (K := SignField)]
  simp [bondRank,SignField]

omit [Fintype E] in
theorem compatibleSigns_sum (left right : E → V) (η : E → Bool) :
    (∑ s : V → Bool,if s∈compatibleSigns left right η then (1:ℝ) else 0)=clusterWeight left right η := by
  rw [Finset.sum_boole,← Fintype.card_subtype]
  unfold clusterWeight
  exact_mod_cast compatibleSigns_card left right η

omit [Fintype V] [Fintype E] in
def bondConnected (left right : E → V) (η : E → Bool) (x y : V) : Prop :=
  ∀ s∈bondSubspace left right η,s x=s y

omit [Fintype V] [Fintype E] in
theorem bondConnected_mono (left right : E → V) (x y : V) :
    Monotone (fun η => bondConnected left right η x y) := by
  intro η ξ h hη s hs
  exact hη s (bondSubspace_antitone left right h hs)

omit [Fintype E] in
theorem bond_sign_correlation (left right : E → V) (η : E → Bool) (x y : V) :
    (∑ s : bondSubspace left right η,fieldSign (s.val x)*fieldSign (s.val y))=
      if bondConnected left right η x y then clusterWeight left right η else 0 := by
  split_ifs with h
  · have he (s : bondSubspace left right η) : fieldSign (s.val x)*fieldSign (s.val y)=1 := by
      rw [h s.val s.property]; exact fieldSign_sq _
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    unfold clusterWeight bondRank
    norm_cast
    rw [Module.card_eq_pow_finrank (K := SignField)]
    simp [SignField]
  · obtain ⟨s,hs,hxy⟩ : ∃ s∈bondSubspace left right η,s x≠s y := by
      unfold bondConnected at h
      push Not at h
      exact h
    let u : bondSubspace left right η := ⟨s,hs⟩
    have hc : fieldSign (s x)*fieldSign (s y)= -1 := by
      have hlocal (a b : SignField) (hab : a≠b) : fieldSign a*fieldSign b= -1 := by
        rcases signField_cases a with rfl | rfl <;> rcases signField_cases b with rfl | rfl <;> simp_all
      exact hlocal _ _ hxy
    have hh := Equiv.sum_comp (Equiv.addRight u) (fun t : bondSubspace left right η => fieldSign (t.val x)*fieldSign (t.val y))
    have he (t : bondSubspace left right η) :
        fieldSign ((t+u).val x)*fieldSign ((t+u).val y)= -(fieldSign (t.val x)*fieldSign (t.val y)) := by
      change fieldSign (t.val x+s x)*fieldSign (t.val y+s y)= _
      rw [fieldSign_add,fieldSign_add,mul_mul_mul_comm,hc,mul_neg_one]
    change (∑ t : bondSubspace left right η,fieldSign ((t+u).val x)*fieldSign ((t+u).val y))=_ at hh
    simp_rw [he] at hh
    rw [Finset.sum_neg_distrib] at hh
    linarith

end ClassicalON

end

end OAI
