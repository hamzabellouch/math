import OAI.NumberTheory.Ostmann.Construction.CoefficientRootSupport
import OAI.NumberTheory.Ostmann.Construction.HalfRows

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem halfModuli_ofFn (p : ℕ) (u : List SmallSlot) :
    List.ofFn (halfModuli p u)=p::u.map SmallSlot.value := by
  rw [halfModuli,List.ofFn_cons]
  congr 1
  exact List.ofFn_getElem_eq_map u SmallSlot.value

theorem halfModuli_prime (p : ℕ) (u : List SmallSlot) (hp : Nat.Prime p)
    (hu : ∀q∈u,Nat.Prime q.value) : ∀i,Nat.Prime (halfModuli p u i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp
  · exact hu u[j] (List.getElem_mem j.isLt)

theorem state_coprime_halves (a : State) (u h : List SmallSlot) (outside : List ℕ)
    (hs : a.small.Perm (u++h)) (hc : a.Coprime outside) :
    Pairwise (fun i j => (halfModuli a.giantPlus u i).Coprime (halfModuli a.giantPlus u j)) ∧
      (∀i,(outsideProduct outside).Coprime (halfModuli a.giantPlus u i)) ∧
      (halfProduct a.giantMinus h).Coprime (halfProduct a.giantPlus u) := by
  have hv : a.values.Perm ((a.giantPlus::u.map SmallSlot.value)++
      (a.giantMinus::h.map SmallSlot.value)) := by
    have h1 := List.Perm.cons a.giantPlus (List.Perm.cons a.giantMinus (hs.map SmallSlot.value))
    have h2 : (a.giantPlus::a.giantMinus::(u.map SmallSlot.value++h.map SmallSlot.value)).Perm
        ((a.giantPlus::u.map SmallSlot.value)++(a.giantMinus::h.map SmallSlot.value)) :=
      List.Perm.cons _ List.perm_middle.symm
    simp only [List.map_append] at h1
    exact h1.trans h2
  have hpw := ((hv.append_right outside).pairwise_iff Nat.Coprime.symm).mp hc
  have hh0 := List.pairwise_append.mp hpw
  have hh1 := List.pairwise_append.mp hh0.1
  have hindex : ∀i j:Fin (u.length+1),i<j→
      (halfModuli a.giantPlus u i).Coprime (halfModuli a.giantPlus u j) := by
    have he : (List.ofFn (halfModuli a.giantPlus u)).Pairwise Nat.Coprime := by
      rw [halfModuli_ofFn]
      exact hh1.1
    exact List.pairwise_ofFn.mp he
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt|hlt
    · exact hindex i j hlt
    · exact (hindex j i hlt).symm
  · intro i
    apply Nat.coprime_list_prod_left_iff.mpr
    intro x hx
    have hi : halfModuli a.giantPlus u i∈a.giantPlus::u.map SmallSlot.value := by
      rw [←halfModuli_ofFn]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (hh0.2.2 _ (List.mem_append_left _ hi) x hx).symm
  · change (a.giantMinus::h.map SmallSlot.value).prod.Coprime
      (a.giantPlus::u.map SmallSlot.value).prod
    apply Nat.coprime_list_prod_left_iff.mpr
    intro x hx
    apply Nat.coprime_list_prod_right_iff.mpr
    intro y hy
    exact (hh1.2.2 y hy x hx).symm

end Ostmann.Construction

end

end OAI
