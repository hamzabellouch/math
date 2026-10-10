import OAI.Dynamics.ConditionalShuffle.ColorRanks

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp Thorp.Conditional

lemma after_eq_iff_mixed (d : ℕ) (h : Coloring d) (c c' : Coins (d+1)) :
    after d h c' = after d h c ↔ ∀ x, sameMask d h x = false → c' x = c x := by
  constructor
  · intro hh x hx; exact mixed_coin_determined d h c' c hh x hx
  · intro hh
    have he : maskedCoin (sameMask d h) c c' = c' := by
      funext x
      cases hx : sameMask d h x with
      | true => simp [maskedCoin, hx]
      | false => simpa only [maskedCoin, hx, Bool.false_eq_true, ite_false] using (hh x hx).symm
    calc
      after d h c' = after d h (maskedCoin (sameMask d h) c c') := congrArg (after d h) he.symm
      _ = after d h c := after_masked d h c c'

def cylinder (d : ℕ) (h : Coloring d) (t : ℕ) (c c' : History (d+1) t) : Prop :=
  ∀ (i : Fin t) (x : Position d), sameMask d (occupancy d h t c i.castSucc) x = false → c' i x = c i x

lemma cylinder_succ (d : ℕ) (h : Coloring d) (t : ℕ) (c c' : History (d+1) (t+1)) :
    cylinder d h (t+1) c c' ↔ cylinder d h t (Fin.init c) (Fin.init c') ∧
      ∀ x, sameMask d (occupied d h t (Fin.init c)) x = false → c' (Fin.last t) x = c (Fin.last t) x := by
  constructor
  · intro hh
    constructor
    · intro i x hx
      apply hh i.castSucc x
      simpa only [occupancy, Fin.snoc_castSucc] using hx
    · intro x hx
      apply hh (Fin.last t) x
      simpa only [occupancy, Fin.snoc_castSucc, occupied] using hx
  · rintro ⟨hp,hl⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro x hx
      exact hl x (by simpa only [occupancy, Fin.snoc_castSucc, occupied] using hx)
    · intro x hx
      exact hp j x (by simpa only [occupancy, Fin.snoc_castSucc] using hx)

theorem occupancy_iff_cylinder (d : ℕ) (h : Coloring d) (t : ℕ) (c c' : History (d+1) t) :
    occupancy d h t c' = occupancy d h t c ↔ cylinder d h t c c' := by
  induction t with
  | zero => simp [cylinder, occupancy]
  | succ t ih =>
      rw [cylinder_succ]
      constructor
      · intro hh
        have hp := congrArg Fin.init hh
        simp only [occupancy, Fin.init_snoc] at hp
        have hb := congrFun hp (Fin.last t)
        change occupied d h t (Fin.init c') = occupied d h t (Fin.init c) at hb
        have hl := congrFun hh (Fin.last (t+1))
        simp only [occupancy, Fin.snoc_last] at hl
        change after d (occupied d h t (Fin.init c')) (c' (Fin.last t)) =
          after d (occupied d h t (Fin.init c)) (c (Fin.last t)) at hl
        rw [hb] at hl
        exact ⟨(ih _ _).mp hp, (after_eq_iff_mixed d _ _ _).mp hl⟩
      · rintro ⟨hp,hl⟩
        have hp' := (ih _ _).mpr hp
        have occupancy_step (a : History (d+1) (t+1)) :
            occupancy d h (t+1) a =
              Fin.snoc (occupancy d h t (Fin.init a))
                (after d (occupancy d h t (Fin.init a) (Fin.last t))
                  (a (Fin.last t))) := rfl
        rw [occupancy_step, occupancy_step, hp']
        congr 1
        exact (after_eq_iff_mixed d _ _ _).mpr hl

end Revealed.Color

end

end OAI
