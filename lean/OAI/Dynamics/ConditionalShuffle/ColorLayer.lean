import OAI.Dynamics.ConditionalShuffle.PredictableResample

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp Thorp.Conditional
abbrev Coloring (d : ℕ) := Position (d+1) → Bool

def after (d : ℕ) (h : Coloring d) (c : Coins (d+1)) : Coloring d :=
  fun x => h ((step (d+1) c).symm x)

def sameMask (d : ℕ) (h : Coloring d) : Position d → Bool :=
  fun x => decide (h (Fin.cons false x) = h (Fin.cons true x))

lemma after_scatter (d : ℕ) (h : Coloring d) (c : Coins (d+1)) (b : Bool) (x : Position d) :
    after d h c (scatterPosition d (b,x)) = h (Fin.cons (b ^^ c x) x) := by
  unfold after
  erw [step_symm_scatter]; rfl

lemma after_masked (d : ℕ) (h : Coloring d) (c r : Coins (d+1)) :
    after d h (maskedCoin (sameMask d h) c r) = after d h c := by
  funext y
  obtain ⟨⟨b,x⟩,rfl⟩ := (scatterPosition d).surjective y
  erw [after_scatter d h (maskedCoin (sameMask d h) c r), after_scatter d h c]
  by_cases hx : h (Fin.cons false x) = h (Fin.cons true x)
  · cases b <;> cases hc : c x <;> cases hr : r x <;>
      simp [maskedCoin, sameMask, hx, hr]
  · simp [maskedCoin, sameMask, hx]

lemma mixed_coin_determined (d : ℕ) (h : Coloring d) (c c' : Coins (d+1))
    (hh : after d h c = after d h c') (x : Position d)
    (hx : sameMask d h x = false) : c x = c' x := by
  have he := congrFun hh (scatterPosition d (false,x))
  rw [after_scatter, after_scatter] at he
  have hn : h (Fin.cons false x) ≠ h (Fin.cons true x) := by simpa [sameMask] using hx
  cases hc : c x <;> cases hc' : c' x <;> simp_all

lemma masked_color_row (d : ℕ) (h : Coloring d) (c c' : Coins (d+1))
    (hh : after d h c = after d h c') (r : Coins (d+1)) :
    maskedCoin (sameMask d h) c r = maskedCoin (sameMask d h) c' r := by
  funext x
  cases hx : sameMask d h x with
  | true => simp [maskedCoin, hx]
  | false => simp only [maskedCoin, hx, Bool.false_eq_true, ite_false]; exact mixed_coin_determined d h c c' hh x hx

def occupancy (d : ℕ) (h : Coloring d) : (t : ℕ) → History (d+1) t → Fin (t+1) → Coloring d :=
  Nat.rec
    (motive := fun t => History (d+1) t → Fin (t+1) → Coloring d)
    (fun _ _ => h)
    (fun t previous c => Fin.snoc (previous (Fin.init c))
      (after d (previous (Fin.init c) (Fin.last t)) (c (Fin.last t))))

def occupied (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t) : Coloring d :=
  occupancy d h t c (Fin.last t)

lemma occupied_zero (d : ℕ) (h : Coloring d) (c : History (d+1) 0) : occupied d h 0 c = h := rfl
lemma occupied_succ (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) (t+1)) :
    occupied d h (t+1) c = after d (occupied d h t (Fin.init c)) (c (Fin.last t)) := by
  simp only [occupied, occupancy, Fin.snoc_last]

lemma occupied_run (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t) :
    occupied d h t c = fun x => h ((run (d+1) t c).symm x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [occupied_succ, run_succ, ih]
      rfl

lemma occupied_image (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t) (x : Position (d+1)) :
    occupied d h t c (run (d+1) t c x) = h x := by simp only [occupied_run, Equiv.symm_apply_apply]

def resample (d : ℕ) (h : Coloring d) (t : ℕ) (c r : History (d+1) t) : History (d+1) t :=
  predictResample d (fun k a => sameMask d (occupied d h k a)) t c r

lemma resample_succ (d : ℕ) (h : Coloring d) (t : ℕ) (c r : History (d+1) (t+1)) :
    resample d h (t+1) c r = Fin.snoc (resample d h t (Fin.init c) (Fin.init r))
      (maskedCoin (sameMask d (occupied d h t (Fin.init c))) (c (Fin.last t)) (r (Fin.last t))) := rfl

lemma resample_observation (d : ℕ) (h : Coloring d) (t : ℕ) (c r : History (d+1) t) :
    occupancy d h t (resample d h t c r) = occupancy d h t c := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have occupancy_step (a : History (d+1) (t+1)) :
          occupancy d h (t+1) a =
            Fin.snoc (occupancy d h t (Fin.init a))
              (after d (occupancy d h t (Fin.init a) (Fin.last t))
                (a (Fin.last t))) := rfl
      rw [resample_succ, occupancy_step, occupancy_step]
      erw [Fin.init_snoc, Fin.snoc_last]
      rw [ih]
      congr 1
      exact after_masked d _ _ _

lemma resample_row (d : ℕ) (h : Coloring d) (t : ℕ) (c c' : History (d+1) t)
    (hh : occupancy d h t c = occupancy d h t c') (r : History (d+1) t) :
    resample d h t c r = resample d h t c' r := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      have hp := congrArg Fin.init hh
      simp only [occupancy, Fin.init_snoc] at hp
      have hb := congrFun hp (Fin.last t)
      change occupied d h t (Fin.init c) = occupied d h t (Fin.init c') at hb
      have hl := congrFun hh (Fin.last (t+1))
      simp only [occupancy, Fin.snoc_last] at hl
      change after d (occupied d h t (Fin.init c)) (c (Fin.last t)) =
        after d (occupied d h t (Fin.init c')) (c' (Fin.last t)) at hl
      rw [resample_succ, resample_succ, ih _ _ hp, hb]
      rw [hb] at hl
      congr 1
      exact masked_color_row d _ _ _ hl _

theorem conditional_resampling (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t)
    {G : Type} [Fintype G] [Nonempty G] (f : History (d+1) t → G) :
    fairMass (fun r => f (resample d h t c r)) =
      Disintegration.conditional (fairMass (fun a => (occupancy d h t a,f a))) (occupancy d h t c) := by
  apply Disintegration.resample_conditional _ _ _ (resample_observation d h t) _ (resample_row d h t) c
  exact predictResample_stationary d _ t

end Revealed.Color

end

end OAI
