import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitAscendingBase

namespace OAI

/-! # One-sided orbit generation and finite ascending bases

For an abelian kernel this is the concrete group form of finite generation
over the monoid ring in the contracting direction. A finite positive-orbit
bound constructs the base; it is not assumed.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finiteOrbitSubgroup_monotone (α : MulAut G) (C : Subgroup G) :
    Monotone (finiteOrbitSubgroup α C) := by
  intro d e hde
  apply iSup_le
  intro i
  exact le_iSup (fun j : Fin e => C.map (α ^ j.val).toMonoidHom)
    ⟨i.val, lt_of_lt_of_le i.isLt hde⟩

theorem iSup_finiteOrbitSubgroup (α : MulAut G) (C : Subgroup G) :
    (⨆ d, finiteOrbitSubgroup α C d) = positiveOrbitSubgroup α C := by
  apply le_antisymm
  · apply iSup_le
    intro d
    apply iSup_le
    intro i
    exact le_iSup (fun n : ℕ => C.map (α ^ n).toMonoidHom) i.val
  · apply iSup_le
    intro n
    exact (le_iSup (fun i : Fin (n + 1) => C.map (α ^ i.val).toMonoidHom)
      ⟨n, Nat.lt_succ_self n⟩).trans (le_iSup (finiteOrbitSubgroup α C) (n + 1))

theorem finiteOrbitSubgroup_inverse_stable (α : MulAut G) (C : Subgroup G) (d : ℕ)
    (hfirst : C.map α.toMonoidHom ≤ finiteOrbitSubgroup α⁻¹ C d) :
    (finiteOrbitSubgroup α⁻¹ C d).map α.toMonoidHom ≤ finiteOrbitSubgroup α⁻¹ C d := by
  rw [finiteOrbitSubgroup, Subgroup.map_iSup]
  apply iSup_le
  intro i
  cases hi : i.val with
  | zero =>
    change (C.map (MonoidHom.id G)).map α.toMonoidHom ≤ finiteOrbitSubgroup α⁻¹ C d
    rw [Subgroup.map_id]
    exact hfirst
  | succ n =>
    rw [Subgroup.map_map]
    have he : α.toMonoidHom.comp ((α⁻¹) ^ (n + 1)).toMonoidHom = ((α⁻¹) ^ n).toMonoidHom := by
      ext x
      change α (((α⁻¹) ^ (n + 1)) x) = ((α⁻¹) ^ n) x
      rw [pow_succ', MulAut.mul_apply]
      exact α.apply_symm_apply _
    rw [he]
    exact le_iSup (fun j : Fin d => C.map ((α⁻¹) ^ j.val).toMonoidHom)
      ⟨n, by omega⟩

theorem ascendingBase_of_oneSided_orbit (α : MulAut G) (C : Subgroup G) (hC : C.FG)
    (hgen : positiveOrbitSubgroup α⁻¹ C = ⊤) : HasFinitelyGeneratedAscendingBase α := by
  have hcover : ∀ g, ∃ d, g ∈ finiteOrbitSubgroup α⁻¹ C d := by
    intro g
    apply (Subgroup.mem_iSup_of_directed (finiteOrbitSubgroup_monotone α⁻¹ C).directed_le).mp
    rw [iSup_finiteOrbitSubgroup, hgen]
    trivial
  obtain ⟨s, hs⟩ := fg_subgroup_map hC α.toMonoidHom
  obtain ⟨d, hd⟩ := finite_subset_subgroup_exhaustion (finiteOrbitSubgroup α⁻¹ C)
    (finiteOrbitSubgroup_monotone α⁻¹ C) hcover s
  have hfirst : C.map α.toMonoidHom ≤ finiteOrbitSubgroup α⁻¹ C (d + 1) := by
    rw [← hs, Subgroup.closure_le]
    exact fun x hx => finiteOrbitSubgroup_monotone α⁻¹ C (Nat.le_succ d) (hd x hx)
  let B := finiteOrbitSubgroup α⁻¹ C (d + 1)
  have hCB : C ≤ B := le_finiteOrbitSubgroup α⁻¹ C (Nat.zero_lt_succ d)
  have hB := finiteOrbitSubgroup_inverse_stable α C (d + 1) hfirst
  have hD : (⨆ n, automorphismStage α B n) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply iSup_le
    intro n
    exact (Subgroup.map_mono hCB).trans (le_iSup (automorphismStage α B) n)
  refine ⟨B, finiteOrbitSubgroup_fg α⁻¹ C hC (d + 1), hB, ?_⟩
  intro g
  apply (Subgroup.mem_iSup_of_directed (automorphismStage_monotone α B hB).directed_le).mp
  rw [hD]
  trivial

theorem ascendingBase_iff_oneSided_orbit (α : MulAut G) :
    HasFinitelyGeneratedAscendingBase α ↔
      ∃ C : Subgroup G, C.FG ∧ positiveOrbitSubgroup α⁻¹ C = ⊤ := by
  constructor
  · rintro ⟨B, hB, _, hc⟩
    refine ⟨B, hB, top_unique ?_⟩
    intro g _
    obtain ⟨n, hn⟩ := hc g
    exact (le_iSup (fun n : ℕ => B.map ((α⁻¹) ^ n).toMonoidHom) n) hn
  · rintro ⟨C, hC, hg⟩
    exact ascendingBase_of_oneSided_orbit α C hC hg

end PolycyclicRecognition

end

end OAI
