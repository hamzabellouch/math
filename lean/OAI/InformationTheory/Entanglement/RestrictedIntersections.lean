import OAI.InformationTheory.Entanglement.BooleanSpan

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction

abbrev Base := {A : Finset (Fin 1028) // A.card=514 ∧ (0 : Fin 1028) ∈ A}
def b : ℕ := Nat.choose 1027 513
def a₀ : ℕ := ∑ j ∈ Finset.range 257, Nat.choose 1028 j
instance prime257 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

lemma sum_monomial_apply {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (B : β → Finset α) (A : Finset α) (c : β) :
    (∑ a ∈ A, monomial (𝔽 := ZMod 257) B {a}) c=((A ∩ B c).card : ZMod 257) := by
  simp only [Finset.sum_apply,monomial,Finset.singleton_subset_iff]
  simp

theorem restricted_intersections (F : Finset Base)
    (h : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A.val ∩ B.val).card ≠ 257) :
    F.card ≤ a₀ := by
  let B : F → Finset (Fin 1028) := fun A => A.val.val
  have hm (A : F) : Pi.single A (1 : ZMod 257) ∈ lowDegree B 256 := by
    have hc : (1 : F → ZMod 257) ∈ lowDegree B 256 := by
      simpa only [monomial_empty] using
        monomial_mem (𝔽 := ZMod 257) B (s := ∅) (d := 256) (by simp)
    have hp := sum_power_mem (𝔽 := ZMod 257) B (B A) 256
    have hd := Submodule.sub_mem (lowDegree (𝔽 := ZMod 257) B 256) hc hp
    convert hd using 1
    ext C
    simp only [Pi.single_apply,Pi.sub_apply,Pi.one_apply,Pi.pow_apply,sum_monomial_apply]
    by_cases he : C=A
    · subst C
      have hcard : (B A).card=514 := A.val.property.1
      simp [hcard,show (514 : ZMod 257)=0 by decide]
    · have hne : A.val ≠ C.val := by intro hh; exact he (Subtype.ext hh.symm)
      have hsets : B A ≠ B C := by intro hh; exact hne (Subtype.ext hh)
      have hpos : 0 < (B A ∩ B C).card := Finset.card_pos.mpr ⟨0,
        Finset.mem_inter.mpr ⟨A.val.property.2,C.val.property.2⟩⟩
      have hle : (B A ∩ B C).card ≤ 514 := by
        simpa only [show (B A).card=514 from A.val.property.1] using
          Finset.card_le_card (Finset.inter_subset_left : B A ∩ B C ⊆ B A)
      have hlt : (B A ∩ B C).card < 514 := by
        by_contra hn
        have ha : B A ∩ B C=B A := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_left (by rw [A.val.property.1]; omega)
        have hb : B A ∩ B C=B C := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_right (by rw [C.val.property.1]; omega)
        exact hsets (ha.symm.trans hb)
      have hx : (B A ∩ B C).card ≠ 257 := h A.val A.property C.val C.property hne
      have hnz : ((B A ∩ B C).card : ZMod 257) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (B A ∩ B C).card 257).mp hz
        obtain ⟨t,ht⟩ := hdvd
        omega
      have hpw := ZMod.pow_card_sub_one_eq_one hnz
      norm_num at hpw
      simp only [he,ite_false,hpw,sub_self]
  have hdim := interpolation_dimension_bound (𝔽 := ZMod 257) B 256 hm
  simpa only [Fintype.card_coe,Fintype.card_fin,show 256+1=257 by rfl,a₀] using hdim

end FiniteConstruction

end

end OAI
