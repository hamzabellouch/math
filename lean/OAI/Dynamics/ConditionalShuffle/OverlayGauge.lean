import OAI.Dynamics.ConditionalShuffle.ResampledInstrument

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Overlay
open Thorp Thorp.Conditional Revealed.Split Revealed.Disintegration Revealed.Instrument Revealed.Scheduled
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

lemma step_relative_roundtrip_cons (d : ℕ) (c c' : Position d → Bool) (b : Bool) (x : Position d) :
    step (d+1) c ((step (d+1) c').symm (step (d+1) c (Fin.cons b x))) =
      step (d+1) c' (Fin.cons b x) := by
  calc
    _ = step (d+1) c ((step (d+1) c').symm (scatterPosition d (b ^^ c x,x))) := by
      rw [step_cons]
    _ = step (d+1) c (Fin.cons ((b ^^ c x) ^^ c' x) x) := by
      erw [step_symm_scatter]; rfl
    _ = scatterPosition d (((b ^^ c x) ^^ c' x) ^^ c x,x) := step_cons d c _ x
    _ = scatterPosition d (b ^^ c' x,x) := by
      apply congrArg (scatterPosition d)
      apply Prod.ext
      · cases b <;> cases c x <;> cases c' x <;> rfl
      · rfl
    _ = _ := (step_cons d c' b x).symm

lemma step_relative_roundtrip (d : ℕ) (c c' : Coins (d+1)) (x : Position (d+1)) :
    step (d+1) c ((step (d+1) c').symm (step (d+1) c x)) = step (d+1) c' x := by
  have h := step_relative_roundtrip_cons d c c' (x 0) (Fin.tail x)
  simpa only [Fin.cons_self_tail] using h

lemma multiplier_forward (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) (a : α) :
    step (d+1) c (L (.inr (multiplier d L active c r a))) =
      step (d+1) (xorCoins d L active c r) (L (.inr a)) := by
  have hm := relative_spec (L.trans (step (d+1) c))
    (L.trans (step (d+1) (xorCoins d L active c r)))
    (fun i => (xorCoins_occupied d L active c r i).symm) a
  change step (d+1) (xorCoins d L active c r) (L (.inr (multiplier d L active c r a))) =
    step (d+1) c (L (.inr a)) at hm
  have he := congrArg (step (d+1) (xorCoins d L active c r)).symm hm
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  exact step_relative_roundtrip d c _ _

lemma multiplier_factor (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) :
    (Equiv.sumCongr (Equiv.refl ι) (multiplier d L active c r)).trans (L.trans (step (d+1) c)) =
      L.trans (step (d+1) (xorCoins d L active c r)) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl i => exact (xorCoins_occupied d L active c r i).symm
  | inr a => exact multiplier_forward d L active c r a

lemma multiplier_gauge (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) :
    multiplier d L active c r = (assignment (L.trans (step (d+1) c)))⁻¹ *
      increment (Split.outside L) (step (d+1) (xorCoins d L active c r)) * assignment L := by
  have hh := congrArg assignment (multiplier_factor d L active c r)
  rw [assignment_pre] at hh
  rw [assignment_post L (step (d+1) (xorCoins d L active c r))] at hh
  rw [mul_assoc]
  exact (eq_inv_mul_iff_mul_eq).2 hh

def xorIncrement (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c r : Coins (d+1)) : Equiv.Perm α :=
  increment e.2 (step (d+1) (xorCoins d (sectionFrame e.2) (σ e.1) c r))

lemma xorIncrement_law (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c : Coins (d+1)) : fairMass (xorIncrement d σ e c) =
      kernel (stepInstrument (d+1) σ) e ((stepInstrument (d+1) σ).obs e c) := xor_kernel d σ e c

lemma xorCoins_frame (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) : xorCoins d L active c r =
      xorCoins d (sectionFrame (Split.outside L)) active c r := by
  rw [xor_resample, xor_resample]
  unfold resample
  rw [mask_frame]

lemma observed_base (d : ℕ) (L : Sum ι α ≃ Position d) (σ : ℕ → Bool) (t : ℕ) (c : History d t) :
    base (stepInstrument d σ) (0,Split.outside L) t (observed (stepInstrument d σ) (0,Split.outside L) t c) =
      (t,Split.outside (L.trans (run d t c))) := by
  apply Prod.ext
  · simpa only [Nat.zero_add] using base_clock d σ 0 (Split.outside L) t _
  · rw [base_outside, observed_outside, Physical.physical_base]

lemma overlayRun_gauge (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) t) :
    overlayRun d L σ t c r = (assignment (L.trans (run (d+1) t c)))⁻¹ *
      resampledRun (stepInstrument (d+1) σ) (xorIncrement d σ) (0,Split.outside L) t c r * assignment L := by
  induction t with
  | zero => simp only [overlayRun, run_zero, resampledRun, mul_one]; exact (inv_mul_cancel _).symm
  | succ t ih =>
      rw [overlayRun, multiplier_gauge, ih, resampledRun, observed_base]
      rw [xorCoins_frame, run_succ]
      change (assignment ((L.trans (run (d+1) t (Fin.init c))).trans (step (d+1) (c (Fin.last t)))))⁻¹ *
        increment _ (step (d+1) (xorCoins d (sectionFrame (Split.outside (L.trans (run (d+1) t (Fin.init c)))))
          (σ t) (c (Fin.last t)) (r (Fin.last t)))) * assignment (L.trans (run (d+1) t (Fin.init c))) *
        ((assignment (L.trans (run (d+1) t (Fin.init c))))⁻¹ * _ * assignment L) =
          (assignment ((L.trans (run (d+1) t (Fin.init c))).trans (step (d+1) (c (Fin.last t)))))⁻¹ *
            (increment _ (step (d+1) (xorCoins d (sectionFrame (Split.outside (L.trans (run (d+1) t (Fin.init c)))))
              (σ t) (c (Fin.last t)) (r (Fin.last t)))) * _) * assignment L
      group

end Revealed.Overlay

end

end OAI
