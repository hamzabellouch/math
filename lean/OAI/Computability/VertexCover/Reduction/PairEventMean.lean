import Mathlib
import OAI.Computability.VertexCover.Reduction.PairSeedFiberCard

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
namespace VertexCover

noncomputable def truthValue (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

noncomputable def finiteMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

private noncomputable def updateSwap {ι α : Type*} [DecidableEq ι] (j : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) where
  toFun p := (Function.update p.1 j p.2, p.1 j)
  invFun p := (Function.update p.1 j p.2, p.1 j)
  left_inv p := by
    apply Prod.ext
    · funext k
      by_cases h : k = j <;> simp [h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext k
      by_cases h : k = j <;> simp [h]
    · simp

theorem sum_updates {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (j : ι) (f : (ι → α) → ℝ) :
    (∑ seed : ι → α, ∑ a : α, f (Function.update seed j a)) =
      Fintype.card α * ∑ seed : ι → α, f seed := by
  classical
  have he := (updateSwap (α := α) j).sum_comp (fun p => f p.1)
  simp only [Fintype.sum_prod_type, updateSwap, Equiv.coe_fn_mk] at he
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] using he

theorem finiteMean_le_of_fibers {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (j : ι) (f : (ι → α) → ℝ) (B : ℝ)
    (h : ∀ seed, ∑ a : α, f (Function.update seed j a) ≤ B) :
    finiteMean f ≤ B / Fintype.card α := by
  classical
  have ha : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (0 : ℝ) < Fintype.card (ι → α) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ι → α)))
    (fun seed _ => h seed)
  rw [sum_updates] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  unfold finiteMean
  apply (div_le_div_iff₀ hs ha).mpr
  nlinarith

end VertexCover

namespace VertexCover.LabelCover

noncomputable def internalPairs {d : ℕ} (J : Finset (Fin d)) : Finset (PositionPair d) := by
  classical
  exact Finset.univ.filter (fun e => e.1.1 ∈ J ∧ e.1.2 ∈ J)

abbrev HiddenSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :=
  ↥(internalPairs J) → Fin Φ.M

noncomputable def spliceSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) : Φ.Seeds d := by
  classical
  exact fun e => if h : e ∈ internalPairs J then hidden ⟨e, h⟩ else frozen e

theorem spliceSeeds_update (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J))
    (c : Fin Φ.M) :
    Φ.spliceSeeds J frozen (Function.update hidden e c) =
      Φ.replaceSeed (Φ.spliceSeeds J frozen hidden) e.1 c := by
  classical
  funext pair
  by_cases hp : pair = e.1
  · subst pair
    simp [spliceSeeds, replaceSeed, e.2]
  · by_cases hj : pair ∈ internalPairs J
    · have hne : (⟨pair, hj⟩ : ↥(internalPairs J)) ≠ e := by
        intro h
        exact hp (congrArg Subtype.val h)
      simp [spliceSeeds, replaceSeed, hp, hj, hne]
    · simp [spliceSeeds, replaceSeed, hp, hj]

theorem pairEvent_mean_le (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d) (hL : ∀ i, (L i).length ≤ ell)
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (e : ↥(internalPairs J)) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
      ≤ (ell : ℝ)^2 * σ := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have h := VertexCover.finiteMean_le_of_fibers e
    (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
    ((ell : ℝ)^2 * σ * Φ.M) (fun hidden => ?_)
  · simpa only [Fintype.card_fin, mul_div_cancel_right₀ _ (show (Φ.M : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt Φ.M_pos))] using h
  · simp_rw [Φ.spliceSeeds_update]
    have hb := Φ.pairSeedFiber_card_le hval L hL (Φ.spliceSeeds J frozen hidden) e.1
    have heq : ((Φ.pairSeedFiber L (Φ.spliceSeeds J frozen hidden) e.1).card : ℝ) =
        ∑ c : Fin Φ.M, VertexCover.truthValue (Φ.PairSeedHit L
          (Φ.replaceSeed (Φ.spliceSeeds J frozen hidden) e.1 c) e.1) := by
      simp only [pairSeedFiber, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro c _
      unfold VertexCover.truthValue
      split_ifs <;> simp
    rwa [heq] at hb

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
