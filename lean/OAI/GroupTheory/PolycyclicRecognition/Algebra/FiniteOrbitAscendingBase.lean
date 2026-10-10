import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingAscendingBases

namespace OAI

/-! # Finite orbit bounds produce an ascending base

This is the group-theoretic bridge from a monic action relation to the
ascending-base condition used in the elementary-amenable finiteness argument.
No finite generation of the whole kernel is required.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

def finiteOrbitSubgroup (α : MulAut G) (C : Subgroup G) (d : ℕ) : Subgroup G :=
  ⨆ i : Fin d, C.map (α ^ i.val).toMonoidHom

theorem finiteOrbitSubgroup_fg (α : MulAut G) (C : Subgroup G) (hC : C.FG) (d : ℕ) :
    (finiteOrbitSubgroup α C d).FG :=
  Subgroup.FG.iSup _ (fun _ => fg_subgroup_map hC _)

theorem le_finiteOrbitSubgroup (α : MulAut G) (C : Subgroup G) {d : ℕ} (hd : 0 < d) :
    C ≤ finiteOrbitSubgroup α C d := by
  have h := le_iSup (fun i : Fin d => C.map (α ^ i.val).toMonoidHom) ⟨0, hd⟩
  change C.map (MonoidHom.id G) ≤ finiteOrbitSubgroup α C d at h
  simpa only [Subgroup.map_id] using h

theorem finiteOrbitSubgroup_stable (α : MulAut G) (C : Subgroup G) (d : ℕ)
    (hrec : C.map (α ^ d).toMonoidHom ≤ finiteOrbitSubgroup α C d) :
    (finiteOrbitSubgroup α C d).map α.toMonoidHom ≤ finiteOrbitSubgroup α C d := by
  rw [finiteOrbitSubgroup, Subgroup.map_iSup]
  apply iSup_le
  intro i
  rw [Subgroup.map_map]
  have he : α.toMonoidHom.comp (α ^ i.val).toMonoidHom = (α ^ (i.val + 1)).toMonoidHom := by
    ext x
    exact (congrArg (fun f : MulAut G => f x) (pow_succ' α i.val)).symm
  rw [he]
  by_cases hi : i.val + 1 < d
  · exact le_iSup (fun j : Fin d => C.map (α ^ j.val).toMonoidHom) ⟨i.val + 1, hi⟩
  · have hid : i.val + 1 = d := by omega
    rw [hid]
    exact hrec

theorem automorphism_exhaustion_of_integer_orbits (α : MulAut G) (C B : Subgroup G)
    (hCB : C ≤ B) (hB : B.map α.toMonoidHom ≤ B)
    (hgen : (⨆ k : ℤ, C.map (α ^ k).toMonoidHom) = ⊤) :
    ∀ g, ∃ n, g ∈ automorphismStage α B n := by
  let D := ⨆ n, automorphismStage α B n
  have hCD : (⨆ k : ℤ, C.map (α ^ k).toMonoidHom) ≤ D := by
    apply iSup_le
    intro k
    cases k with
    | ofNat n =>
      rintro _ ⟨x, hx, rfl⟩
      have hxB : (α ^ n) x ∈ B := automorphism_pow_mem_of_stable α B hB n (hCB hx)
      apply (le_iSup (automorphismStage α B) 0)
      change (α ^ (n : ℤ)) x ∈ automorphismStage α B 0
      rw [zpow_natCast, automorphismStage_zero]
      exact hxB
    | negSucc n =>
      rintro _ ⟨x, hx, rfl⟩
      apply (le_iSup (automorphismStage α B) (n + 1))
      refine ⟨x, hCB hx, ?_⟩
      simp
  have hD : D = ⊤ := top_unique (hgen ▸ hCD)
  intro g
  have hg : g ∈ D := hD ▸ Subgroup.mem_top g
  exact (Subgroup.mem_iSup_of_directed (automorphismStage_monotone α B hB).directed_le).mp hg

theorem ascendingBase_of_finite_orbit_relation (α : MulAut G) (C : Subgroup G)
    (hC : C.FG) {d : ℕ} (hd : 0 < d)
    (hrec : C.map (α ^ d).toMonoidHom ≤ finiteOrbitSubgroup α C d)
    (hgen : (⨆ k : ℤ, C.map (α ^ k).toMonoidHom) = ⊤) :
    HasFinitelyGeneratedAscendingBase α := by
  have hs := finiteOrbitSubgroup_stable α C d hrec
  exact ⟨finiteOrbitSubgroup α C d, finiteOrbitSubgroup_fg α C hC d, hs,
    automorphism_exhaustion_of_integer_orbits α C _ (le_finiteOrbitSubgroup α C hd) hs hgen⟩

end PolycyclicRecognition

end

end OAI
