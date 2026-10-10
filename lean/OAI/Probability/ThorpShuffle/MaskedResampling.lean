import OAI.Probability.ThorpShuffle.MarginalEnergy

namespace OAI

universe uα uι

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def maskedCoin {α : Type uα} (mask : α → Bool) (c r : α → Bool) : α → Bool :=
  fun x => if mask x then r x else c x

def maskSwap {α : Type uα} (mask : α → Bool) :
    Equiv.Perm ((α → Bool) × (α → Bool)) :=
  Function.Involutive.toPerm
    (fun p => (maskedCoin mask p.1 p.2, maskedCoin mask p.2 p.1)) (by
      intro p
      apply Prod.ext <;> funext x <;>
        cases hm : mask x <;> simp [maskedCoin, hm])

theorem mean_maskedCoin {α : Type uα} [Fintype α] [DecidableEq α]
    (mask : α → Bool) (f : (α → Bool) → ℝ) :
    mean (fun c : α → Bool => mean (fun r : α → Bool => f (maskedCoin mask c r))) =
      mean f := by
  have he := mean_equiv (maskSwap mask) (fun p => f p.1)
  change mean (fun p : (α → Bool) × (α → Bool) => f (maskedCoin mask p.1 p.2)) = _ at he
  rw [mean_prod, mean_prod] at he
  simpa only [mean_const] using he

def freePairMask (d : ℕ) (B : Position (d + 1) → Bool) : Position d → Bool :=
  fun x => B (Fin.cons false x) && B (Fin.cons true x)

theorem step_cons (d : ℕ) (c : Position d → Bool) (b : Bool) (x : Position d) :
    step (d + 1) c (Fin.cons b x) = scatterPosition d (b ^^ c x, x) := by
  simp [step, scatterPosition, splitPosition, pairSwitch]

theorem masked_step_occupied (d : ℕ) (B : Position (d + 1) → Bool)
    (c r : Position d → Bool) (x : Position (d + 1)) (hx : B x = false) :
    step (d + 1) (maskedCoin (freePairMask d B) c r) x = step (d + 1) c x := by
  obtain ⟨⟨b, y⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change B (Fin.cons b y) = false at hx
  change step (d + 1) (maskedCoin (freePairMask d B) c r) (Fin.cons b y) =
    step (d + 1) c (Fin.cons b y)
  rw [step_cons, step_cons]
  cases b <;> simp [maskedCoin, freePairMask, hx]

theorem physicalFlow_resampling (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Position d → Bool) (y : Position (d + 1)) :
    physicalFlow d B w c y = mean (fun r : Position d → Bool =>
      w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y)) := by
  obtain ⟨⟨b, x⟩, rfl⟩ := (scatterPosition d).surjective y
  have hs : mean (fun r : Position d → Bool =>
      w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm
        (scatterPosition d (b, x)))) =
      mean (fun r : Position d → Bool =>
        w (Fin.cons (b ^^ maskedCoin (freePairMask d B) c r x) x)) := by
    apply mean_congr
    intro r
    exact congrArg w (step_symm_scatter d (maskedCoin (freePairMask d B) c r) (b, x))
  rw [hs]
  erw [physicalFlow_scatter]
  change (if b then (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2
    else (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1) =
    mean (fun r : Position d → Bool =>
      w (Fin.cons (b ^^ (if freePairMask d B x then r x else c x)) x))
  rw [mean_coin_eval x (fun z => w (Fin.cons (b ^^ (if freePairMask d B x then z else c x)) x))]
  cases h0 : B (Fin.cons false x) <;> cases h1 : B (Fin.cons true x) <;>
    cases b <;> cases c x <;>
    simp [pairUpdate, freePairMask, h0, h1, mean_bool] <;> ring

theorem masked_step_exposed {ι : Type uι} (d : ℕ) (B : Position (d + 1) → Bool)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false) (c r : Position d → Bool) :
    (step (d + 1) (maskedCoin (freePairMask d B) c r)) ∘ e = (step (d + 1) c) ∘ e := by
  funext i
  exact masked_step_occupied d B c r (e i) (he i)

theorem physicalFlow_joint {ι : Type uι} (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (e : ι → Position (d + 1))
    (he : ∀ i, B (e i) = false) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun c : Position d → Bool => ∑ y, physicalFlow d B w c y * f ((step (d + 1) c) ∘ e) y) =
      mean (fun c : Position d → Bool => ∑ x, w x * f ((step (d + 1) c) ∘ e) (step (d + 1) c x)) := by
  calc
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ y, w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y) *
          f ((step (d + 1) c) ∘ e) y)) := by
      apply mean_congr
      intro c
      rw [mean_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [mean_mul_const, physicalFlow_resampling]
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, w x * f ((step (d + 1) c) ∘ e)
          (step (d + 1) (maskedCoin (freePairMask d B) c r) x))) := by
      apply mean_congr
      intro c
      apply mean_congr
      intro r
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp (step (d + 1) (maskedCoin (freePairMask d B) c r))
          (fun y => w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y) *
            f ((step (d + 1) c) ∘ e) y)).symm
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, w x * f ((step (d + 1) (maskedCoin (freePairMask d B) c r)) ∘ e)
          (step (d + 1) (maskedCoin (freePairMask d B) c r) x))) := by
      apply mean_congr
      intro c
      apply mean_congr
      intro r
      rw [masked_step_exposed d B e he c r]
    _ = _ := by
      exact mean_maskedCoin (freePairMask d B) (fun c => ∑ x, w x *
        f ((step (d + 1) c) ∘ e) (step (d + 1) c x))

end Conditional

end Thorp

end

end OAI
