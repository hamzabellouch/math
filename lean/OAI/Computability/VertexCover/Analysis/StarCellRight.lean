import Mathlib
import OAI.Computability.VertexCover.Analysis.StarMeanContinuous

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def starLocalKey (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (e : PositionPair d) (c : Fin Φ.M) :
    Option (Fin Φ.M) × Option (Fin Φ.u) × Option (Fin Φ.v) := by
  classical
  exact (if e.1.1 = k ∨ e.1.2 = k then none else some c,
    if e.1.1 = k then none else some (Φ.left c),
    if e.1.2 = k then none else some (Φ.right c))

theorem starKey_apply (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) :
    Φ.starKey k seed e = Φ.starLocalKey k e (seed e) := rfl

noncomputable def starCell (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) : Finset (Fin Φ.M) := by
  classical
  exact Finset.univ.filter (fun c => Φ.starLocalKey k e c = Φ.starLocalKey k e (seed e))

theorem mem_starCell (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) (c : Fin Φ.M) :
    c ∈ Φ.starCell k seed e ↔ Φ.starLocalKey k e c = Φ.starLocalKey k e (seed e) := by
  classical
  simp [starCell]

theorem mem_starFiber_iff_cells (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed seed' : Φ.Seeds d) :
    seed' ∈ Φ.starFiber k seed ↔ ∀ e, seed' e ∈ Φ.starCell k seed e := by
  rw [Φ.mem_starFiber]
  constructor
  · intro h e
    exact (Φ.mem_starCell k seed e _).mpr (congrFun h e)
  · intro h
    funext e
    exact (Φ.mem_starCell k seed e _).mp (h e)

noncomputable def starFiberEquiv (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) : (Φ.starFiber k seed) ≃ (∀ e, Φ.starCell k seed e) where
  toFun seed' e := ⟨seed'.1 e, (Φ.mem_starFiber_iff_cells k seed seed'.1).mp seed'.2 e⟩
  invFun choices := ⟨fun e => (choices e).1,
    (Φ.mem_starFiber_iff_cells k seed _).mpr (fun e => (choices e).2)⟩
  left_inv seed' := by
    apply Subtype.ext
    rfl
  right_inv choices := by
    funext e
    apply Subtype.ext
    rfl

theorem starFiber_card_product (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) :
    (Φ.starFiber k seed).card = ∏ e, (Φ.starCell k seed e).card := by
  classical
  have h := Fintype.card_congr (Φ.starFiberEquiv k seed)
  simpa only [Fintype.card_coe, Fintype.card_pi] using h

theorem starCell_nonempty (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) : (Φ.starCell k seed e).Nonempty :=
  ⟨seed e, (Φ.mem_starCell k seed e _).mpr rfl⟩

theorem finiteMean_starFiber_product (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (f : Φ.Seeds d → ℝ) :
    VertexCover.finiteMean (fun seed' : Φ.starFiber k seed => f seed'.1) =
      VertexCover.finiteMean (fun choices : (∀ e, Φ.starCell k seed e) =>
        f (fun e => (choices e).1)) := by
  classical
  have hs := (Φ.starFiberEquiv k seed).sum_comp
    (fun choices : (∀ e, Φ.starCell k seed e) => f (fun e => (choices e).1))
  have hc := Fintype.card_congr (Φ.starFiberEquiv k seed)
  unfold VertexCover.finiteMean
  rw [hc]
  exact congrArg (fun x : ℝ => x / Fintype.card (∀ e, Φ.starCell k seed e)) hs

theorem starCell_nonincident (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) (hL : e.1.1 ≠ k) (hR : e.1.2 ≠ k) :
    Φ.starCell k seed e = {seed e} := by
  classical
  ext c
  rw [Φ.mem_starCell, Finset.mem_singleton]
  constructor
  · intro h
    have hh := congrArg Prod.fst h
    simpa only [starLocalKey, ite_eq_right (not_or.mpr ⟨hL, hR⟩), Option.some.injEq] using hh
  · rintro rfl
    rfl

theorem starCell_left (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) (hL : e.1.1 = k) :
    Φ.starCell k seed e = Finset.univ.filter (fun c => Φ.right c = Φ.right (seed e)) := by
  classical
  have hR : e.1.2 ≠ k := by
    intro h
    exact (ne_of_lt e.2) (hL.trans h.symm)
  ext c
  simp [Φ.mem_starCell, starLocalKey, hL, hR]

theorem starCell_right (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed : Φ.Seeds d) (e : PositionPair d) (hR : e.1.2 = k) :
    Φ.starCell k seed e = Finset.univ.filter (fun c => Φ.left c = Φ.left (seed e)) := by
  classical
  have hL : e.1.1 ≠ k := by
    intro h
    exact (ne_of_lt e.2) (h.trans hR.symm)
  ext c
  simp [Φ.mem_starCell, starLocalKey, hL, hR]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
