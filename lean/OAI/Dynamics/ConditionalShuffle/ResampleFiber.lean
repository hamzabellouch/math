import OAI.Dynamics.ConditionalShuffle.ScheduledInstrument

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Disintegration
open Thorp Thorp.Conditional
variable {Ω R E G : Type} [Fintype Ω] [Nonempty Ω] [Fintype R] [fintype_E : Fintype E]
  [Fintype G] [Nonempty G]

lemma fairMass_at_image_pos (a : Ω → E) (c : Ω) : 0 < fairMass a (a c) := by
  let retained_fintype_E := fintype_E
  unfold fairMass
  apply div_pos _ (by exact_mod_cast Fintype.card_pos)
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=fun x : Ω => if a x = a c then (1 : ℝ) else 0)
    (fun x _ => by split_ifs <;> norm_num) (Finset.mem_univ c)
  simp only [ite_true] at h
  linarith

lemma resample_conditional (a : Ω → E) (b : Ω → G) (F : Ω → R → Ω)
    (hobs : ∀ c r, a (F c r) = a c)
    (hstat : ∀ f : Ω → ℝ, mean (fun c => mean (fun r => f (F c r))) = mean f)
    (hrow : ∀ c c', a c = a c' → ∀ r, F c r = F c' r) (c : Ω) :
    fairMass (fun r => b (F c r)) = conditional (fairMass (fun x => (a x,b x))) (a c) := by
  funext g
  have hK (x : Ω) (hx : a x = a c) : fairMass (fun r => b (F x r)) g = fairMass (fun r => b (F c r)) g := by
    congr 1; funext r; rw [hrow x c hx r]
  have hj : fairMass (fun x => (a x,b x)) (a c,g) =
      fairMass a (a c) * fairMass (fun r => b (F c r)) g := by
    rw [fairMass_eq_mean, ← hstat]
    simp only [Prod.mk.injEq, hobs, ite_and, mean_indicator]
    change mean (fun x : Ω => if a x = a c then fairMass (fun r => b (F x r)) g else 0) = _
    calc
      _ = mean (fun x : Ω => (if a x = a c then (1 : ℝ) else 0) * fairMass (fun r => b (F c r)) g) := by
        apply mean_congr; intro x
        by_cases hx : a x = a c
        · rw [ite_eq_left hx, ite_eq_left hx, one_mul, hK x hx]
        · simp only [ite_eq_right hx, zero_mul]
      _ = _ := by rw [mean_mul_const, ← fairMass_eq_mean]
  rw [conditional, marginal_fairMass, ite_eq_right (ne_of_gt (fairMass_at_image_pos a c)), hj]
  exact (mul_div_cancel_left₀ _ (ne_of_gt (fairMass_at_image_pos a c))).symm

end Revealed.Disintegration

end

end OAI
