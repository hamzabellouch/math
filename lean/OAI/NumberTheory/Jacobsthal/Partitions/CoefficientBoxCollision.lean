import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

def boxLift {ι : Type*} {H : ℕ} (x : ι → Fin (H+1)) : ι → ℤ := fun i => (x i).val

theorem boxLift_injective {ι : Type*} {H : ℕ} : Function.Injective (@boxLift ι H) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi : ((x i).val : ℤ) = ((y i).val : ℤ) := congrFun h i
  exact_mod_cast hi

theorem exists_bounded_kernel_vector {ι Γ : Type*} [Fintype ι]
    [AddCommGroup Γ] [Fintype Γ] (φ : (ι → ℤ) →+ Γ) (H : ℕ)
    (hcard : Fintype.card Γ < (H+1)^(Fintype.card ι)) :
    ∃ v : ι → ℤ, v ≠ 0 ∧ (∀ i, |v i| ≤ (H : ℤ)) ∧ φ v = 0 := by
  classical
  let f : (ι → Fin (H+1)) → Γ := fun x => φ (boxLift x)
  have hnot : ¬Function.Injective f := by
    intro hinj
    have hc := Fintype.card_le_of_injective f hinj
    have he : Fintype.card (ι → Fin (H+1)) = (H+1)^(Fintype.card ι) := by simp
    rw [he] at hc
    exact (not_le_of_gt hcard) hc
  unfold Function.Injective at hnot
  push Not at hnot
  obtain ⟨x,y,hxy,hne⟩ := hnot
  let v := boxLift x - boxLift y
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    apply boxLift_injective
    exact sub_eq_zero.mp hz
  refine ⟨v,hv,?_,?_⟩
  · intro i
    have hx := (x i).isLt
    have hy := (y i).isLt
    change |((x i).val : ℤ) - ((y i).val : ℤ)| ≤ (H : ℤ)
    rw [abs_le]
    omega
  · change φ (boxLift x - boxLift y) = 0
    rw [map_sub]
    change φ (boxLift x) = φ (boxLift y) at hxy
    rw [hxy,sub_self]

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
