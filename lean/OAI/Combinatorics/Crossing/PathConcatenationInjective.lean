import OAI.Combinatorics.Crossing.PolygonalChains

namespace OAI

namespace Zarankiewicz

theorem path_meeting_parameters {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b)
    (s t : unitInterval) (he : γ s=η t) : s=1 ∧ t=0 := by
  have hx : γ s=b := hm _ ⟨s,rfl⟩ ⟨t,he.symm⟩
  exact ⟨hγ (hx.trans γ.target.symm),hη (he.symm.trans (hx.trans η.source.symm))⟩

theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b) :
    Function.Injective (γ.trans η) := by
  intro s t he
  by_cases hs : (s : ℝ) ≤ 1/2 <;> by_cases ht : (t : ℝ) ≤ 1/2
  · simp only [Path.trans_apply,dite_eq_left hs,dite_eq_left ht] at he
    have hh := congrArg Subtype.val (hγ he)
    apply Subtype.ext
    change 2*(s : ℝ)=2*(t : ℝ) at hh
    linarith
  · simp only [Path.trans_apply,dite_eq_left hs,dite_eq_right ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he).2
    change 2*(t : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dite_eq_right hs,dite_eq_left ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he.symm).2
    change 2*(s : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dite_eq_right hs,dite_eq_right ht] at he
    have hh := congrArg Subtype.val (hη he)
    apply Subtype.ext
    change 2*(s : ℝ)-1=2*(t : ℝ)-1 at hh
    linarith

end Zarankiewicz

end OAI
