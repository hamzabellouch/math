import OAI.Probability.ThorpShuffle.FourierBounds

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma family_unitary {α : Type} [Fintype α] (p : Shape α) (g : Equiv.Perm α) (v w : Space (α:=α) p) :
    ⟪family p g v, family p g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  change ⟪tabloidRep _ _ g v.val, tabloidRep _ _ g w.val⟫_ℂ = ⟪v.val, w.val⟫_ℂ
  exact PermutationSpace.rep_unitary g v.val w.val

lemma regular_char_fin (n : ℕ) (g : Equiv.Perm (Fin n)) :
    ∑ p : NShape n, (Module.finrank ℂ (Space (α:=Fin n) p) : ℂ) * (family (α:=Fin n) p).character g =
      if g = 1 then (Fintype.card (Equiv.Perm (Fin n)) : ℂ) else 0 := by
  have hc : Fintype.card (Equiv.Perm (Fin n)) = Nat.card (Equiv.Perm (Fin n)) := Fintype.card_eq_nat_card
  rw [hc]
  by_cases h : g = 1
  · simpa only [degree, ite_eq_left h] using regular_char g
  · simpa only [degree, ite_eq_right h] using regular_char g

def symmetricFamily (n : ℕ) : Thorp.Fourier.Family (Equiv.Perm (Fin n)) where
  Index := NShape n
  Space := fun p => Space (α:=Fin n) p
  rep := fun p => family (α:=Fin n) p
  positive := by
    intro p
    simpa only [degree] using degree_pos p
  unitary := fun p g v w => family_unitary (α:=Fin n) p g v w
  distinct := fun p q h => family_inequiv (α:=Fin n) p q h
  regular := by
    intro g
    by_cases h : g = 1
    · simpa only [ite_eq_left h] using regular_char_fin n g
    · simpa only [ite_eq_right h] using regular_char_fin n g

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical

variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def subrepPull (ρ : Representation ℂ G V) (e : H ≃* G) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun U := { toSubmodule := U.toSubmodule
               apply_mem_toSubmodule := fun h => U.apply_mem_toSubmodule (e h) }
  invFun U := { toSubmodule := U.toSubmodule
                apply_mem_toSubmodule := by
                  intro g v hv
                  have hh := U.apply_mem_toSubmodule (e.symm g) hv
                  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hh }
  left_inv U := by rfl
  right_inv U := by rfl
  map_rel_iff' := by rfl

def Family.pull (F : Family G) (e : H ≃* G) : Family H where
  Index := F.Index
  Space := F.Space
  rep i := (F.rep i).comp e.toMonoidHom
  irreducible i := (subrepPull (F.rep i) e).symm.isSimpleOrder
  positive := F.positive
  unitary := fun i h => F.unitary i (e h)
  distinct := by
    intro i j hh
    obtain ⟨A⟩ := hh
    apply F.distinct i j
    refine ⟨{ A.toLinearEquiv with isIntertwining' := ?_ }⟩
    intro g
    ext v
    have ha := DFunLike.congr_fun (A.isIntertwining' (e.symm g)) v
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using ha
  regular := by
    intro h
    have hh := F.regular (e h)
    have hc : Fintype.card G = Fintype.card H := (Fintype.card_congr e.toEquiv).symm
    change ∑ i, (Module.finrank ℂ (F.Space i) : ℂ) * (F.rep i).character (e h) = _
    simpa only [e.map_eq_one_iff, hc] using hh

end Thorp.Fourier

end

end OAI
