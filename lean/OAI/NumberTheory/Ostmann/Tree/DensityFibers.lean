import OAI.NumberTheory.Ostmann.Tree.DensitySplit

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

def multiplicity : ℕ → ℕ
  | 0 => 1
  | d+1 => 2 * multiplicity d ^ 2

theorem multiplicity_eq (d : ℕ) : multiplicity d = 2^(2^d-1) := by
  induction d with
  | zero => simp [multiplicity]
  | succ d ih =>
    rw [multiplicity, ih, ← pow_mul]
    have hp : 0 < 2^d := pow_pos (by decide) d
    have he : (2^d-1)*2+1 = 2^(d+1)-1 := by rw [pow_succ]; omega
    rw [← he, pow_succ, mul_comm]

theorem card_le_child_images {d : ℕ} (S : Finset (Leaves (d+1) → Fˣ)) :
    S.card ≤ (S.image left).card * (S.image right).card := by
  classical
  rw [← Finset.card_product]
  apply le_trans (le_of_eq (Finset.card_image_of_injective S assignment_injective).symm)
  apply Finset.card_le_card
  intro x hx
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hM, Finset.mem_image_of_mem _ hM⟩

theorem reconstruct_fiber_card_le {d : ℕ} (P : Parameters F d) (hP : P.consistent)
    (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (S : Finset (Leaves d → Fˣ)) (y : Leaves d → Fˣ)
    (hS : ∀ M ∈ S, reconstruct D P Xl Xr c M = some y) :
    S.card ≤ multiplicity d := by
  classical
  induction P generalizing D Xl Xr c with
  | leaf s sign =>
    apply Finset.card_le_one.mpr
    intro M hM N hN
    have he := leafProduct_eq_of_reconstruct_eq (.leaf s sign) hP D Xl Xr c hc
      M N y (hS M hM) (hS N hN)
    have hprod (V : Leaves 0 → Fˣ) : Parameters.leafProduct V = V (fun i => Fin.elim0 i) := by
      simp only [Parameters.leafProduct, Finset.univ_unique, Finset.prod_singleton]
      exact congrArg V (Subsingleton.elim _ _)
    rw [hprod, hprod] at he
    funext v
    have hv : v = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hv] using he
  | @branch d s a b u L R ihl ihr =>
    let f : (Leaves (d+1) → Fˣ) → Fˣ := fun M => Parameters.leafProduct (left M)
    have hfib : ∀ z ∈ S.image f, (S.filter (fun M => f M=z)).card ≤ multiplicity d ^ 2 := by
      intro z hz
      obtain ⟨N, hN, hNz⟩ := Finset.mem_image.mp hz
      obtain ⟨hpN, hNl, hNr⟩ := reconstruct_branch_some s a b u D Xl Xr c L R N y (hS N hN)
      let pN := Units.mk0 _ hpN
      let S' := S.filter (fun M => f M=z)
      have hchild : ∀ M ∈ S',
          reconstruct D L pN Xl (u*a) (left M) = some (left y) ∧
          reconstruct D R pN Xr (u*b) (right M) = some (right y) := by
        intro M hM
        obtain ⟨hMS, hMz⟩ := Finset.mem_filter.mp hM
        obtain ⟨hpM, hMl, hMr⟩ := reconstruct_branch_some s a b u D Xl Xr c L R M y (hS M hMS)
        have he := pivot_eq_of_left_product_eq s a b u D Xl Xr c L R hP hc M N y
          (hS M hMS) (hS N hN) (hMz.trans hNz.symm)
        have hp : Units.mk0 _ hpM = pN := Units.ext he
        exact ⟨hp ▸ hMl, hp ▸ hMr⟩
      have hl : (S'.image left).card ≤ multiplicity d := by
        apply ihl hP.2.2.1 D pN Xl (u*a) hP.1 (S'.image left) (left y)
        intro V hV
        obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hV
        exact (hchild M hM).1
      have hr : (S'.image right).card ≤ multiplicity d := by
        apply ihr hP.2.2.2 D pN Xr (u*b) hP.2.1 (S'.image right) (right y)
        intro V hV
        obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hV
        exact (hchild M hM).2
      exact (card_le_child_images S').trans (by simpa only [pow_two] using Nat.mul_le_mul hl hr)
    calc
      S.card ≤ multiplicity d ^ 2 * (S.image f).card := Finset.card_le_mul_card_image S _ hfib
      _ ≤ multiplicity d ^ 2 * 2 := Nat.mul_le_mul_left _
        (left_product_image_card_le_two s a b u D Xl Xr c L R hP hc S y hS)
      _ = multiplicity (d+1) := by simp only [multiplicity, mul_comm]

theorem reconstruct_fiber_card_bound {d : ℕ} (P : Parameters F d) (hP : P.consistent)
    (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (S : Finset (Leaves d → Fˣ)) (y : Leaves d → Fˣ)
    (hS : ∀ M ∈ S, reconstruct D P Xl Xr c M = some y) :
    S.card ≤ 2^(2^d-1) := by
  rw [← multiplicity_eq]
  exact reconstruct_fiber_card_le P hP D Xl Xr c hc S y hS

end
end Ostmann.Tree.Density

end OAI
