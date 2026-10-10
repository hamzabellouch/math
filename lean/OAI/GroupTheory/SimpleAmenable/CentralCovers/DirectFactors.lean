import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DirectFactors
variable {G : Type*} [Group G]

structure CommutingFactors (A B : Subgroup G) : Prop where
  commute : ∀ a ∈ A, ∀ b ∈ B, Commute a b
  cover : ∀ x : G, ∃ a ∈ A, ∃ b ∈ B, x = a * b

namespace CommutingFactors
variable {A B C D : Subgroup G}

theorem symm (h : CommutingFactors A B) : CommutingFactors B A where
  commute b hb a ha := (h.commute a ha b hb).symm
  cover x := by
    obtain ⟨a, ha, b, hb, rfl⟩ := h.cover x
    exact ⟨b, hb, a, ha, (h.commute a ha b hb).eq⟩

theorem mem_center_of_mem_inter (h : CommutingFactors A B) {x : G}
    (ha : x ∈ A) (hb : x ∈ B) : x ∈ Subgroup.center G := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨a, ha', b, hb', rfl⟩ := h.cover y
  exact ((h.commute a ha' x hb).mul_left (h.commute x ha b hb').symm).eq

theorem inter_eq_bot (h : CommutingFactors A B) (hz : Subgroup.center G = ⊥) :
    A ⊓ B = ⊥ := by
  apply bot_unique
  intro x hx
  simpa [hz] using h.mem_center_of_mem_inter hx.1 hx.2

theorem mem_left_of_commute_right (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {x : G}
    (hx : ∀ b ∈ B, Commute x b) : x ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.cover x
  have hbz : b ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨c, hc, d, hd, rfl⟩ := h.cover y
    have hbd : Commute b d := by
      have ht := (hx d hd).eq
      have ht' : a * (b * d) = a * (d * b) := by
        calc
          a * (b * d) = (a * b) * d := (mul_assoc _ _ _).symm
          _ = d * (a * b) := ht
          _ = (d * a) * b := (mul_assoc _ _ _).symm
          _ = (a * d) * b := by rw [(h.commute a ha d hd).eq]
          _ = a * (d * b) := mul_assoc _ _ _
      exact mul_left_cancel ht'
    exact ((h.commute c hc b hb).mul_left hbd.symm).eq
  have hb1 : b = 1 := by simpa [hz] using hbz
  simpa [hb1] using ha

def productHom (h : CommutingFactors A B) : A × B →* G where
  toFun x := x.1.1 * x.2.1
  map_one' := one_mul _
  map_mul' x y := by
    change (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
      (x.1.1 * x.2.1) * (y.1.1 * y.2.1)
    calc
      _ = x.1.1 * (y.1.1 * x.2.1) * y.2.1 := by group
      _ = x.1.1 * (x.2.1 * y.1.1) * y.2.1 := by
        rw [(h.commute _ y.1.2 _ x.2.2).eq]
      _ = _ := by group

@[simp] theorem productHom_apply (h : CommutingFactors A B) (x : A × B) :
    h.productHom x = x.1.1 * x.2.1 := rfl

theorem productHom_bijective (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : Function.Bijective h.productHom := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff h.productHom).mp
    apply bot_unique
    rintro ⟨a, b⟩ hab
    change (a : G) * b = 1 at hab
    have hab' : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have haB : (a : G) ∈ B := hab' ▸ B.inv_mem b.property
    have ha1 : (a : G) = 1 := by
      simpa [hz] using h.mem_center_of_mem_inter a.property haB
    have hb1 : (b : G) = 1 := by simpa [ha1] using hab
    change (a, b) = 1
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  · intro x
    obtain ⟨a, ha, b, hb, hab⟩ := h.cover x
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩), hab.symm⟩

noncomputable def productEquiv (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : A × B ≃* G :=
  MulEquiv.ofBijective h.productHom (h.productHom_bijective hz)

@[simp] theorem productEquiv_apply (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : A × B) :
    h.productEquiv hz x = x.1.1 * x.2.1 := rfl

theorem left_component_commutes (h : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) {c y : G} (hc : c ∈ C) {d : G} (hd : d ∈ D)
    (hcy : Commute (c * d) y) : Commute c y := by
  obtain ⟨c', hc', d', hd', rfl⟩ := h.cover y
  let e := h.productEquiv hz
  have he : Commute ((⟨c,hc⟩,⟨d,hd⟩) : C × D)
      ((⟨c',hc'⟩,⟨d',hd'⟩) : C × D) := by
    apply e.injective
    simpa only [map_mul, e, productEquiv_apply] using hcy.eq
  have hcc' : Commute c c' := by
    exact congrArg (fun z : C × D => (z.1 : G)) he
  exact hcc'.mul_right (h.commute c hc d' hd')

theorem refine_four (h : CommutingFactors A B) (k : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) (x : G) :
    ∃ ac ∈ A ⊓ C, ∃ ad ∈ A ⊓ D, ∃ bc ∈ B ⊓ C, ∃ bd ∈ B ⊓ D,
      x = ac * ad * bc * bd := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.cover x
  obtain ⟨ac, hacC, ad, hadD, heqa⟩ := k.cover a
  obtain ⟨bc, hbcC, bd, hbdD, heqb⟩ := k.cover b
  have hacA : ac ∈ A := by
    apply h.mem_left_of_commute_right hz
    intro y hy
    apply k.left_component_commutes hz hacC hadD
    rw [← heqa]
    exact h.commute a ha y hy
  have hadA : ad ∈ A := by
    have : ad = ac⁻¹ * a := by rw [heqa]; group
    rw [this]
    exact A.mul_mem (A.inv_mem hacA) ha
  have hbcB : bc ∈ B := by
    apply h.symm.mem_left_of_commute_right hz
    intro y hy
    apply k.left_component_commutes hz hbcC hbdD
    rw [← heqb]
    exact (h.commute y hy b hb).symm
  have hbdB : bd ∈ B := by
    have : bd = bc⁻¹ * b := by rw [heqb]; group
    rw [this]
    exact B.mul_mem (B.inv_mem hbcB) hb
  exact ⟨ac, ⟨hacA,hacC⟩, ad, ⟨hadA,hadD⟩, bc, ⟨hbcB,hbcC⟩,
    bd, ⟨hbdB,hbdD⟩, by rw [heqa, heqb]; group⟩

end CommutingFactors
end DirectFactors

end SimpleAmenable
end
end

end OAI
