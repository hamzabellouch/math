import OAI.Dynamics.ConditionalShuffle.ResampleFiber

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Overlay
open Thorp Thorp.Conditional Revealed.Split Revealed.Disintegration Revealed.Instrument Revealed.Scheduled
variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

def mask (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool) : Position d → Bool :=
  fun x => active && freePairMask d (avoid (fun i => L (.inl i))) x

def resample (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) : Coins (d+1) := maskedCoin (mask d L active) c r

lemma resample_false (d : ℕ) (L : Sum ι α ≃ Position (d+1))
    (c r : Coins (d+1)) : resample d L false c r = c := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  funext x
  change (if false && freePairMask d (avoid (fun i => L (.inl i))) x then r x else c x) = c x
  simp

lemma resample_occupied (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) (i : ι) :
    step (d+1) (resample d L active c r) (L (.inl i)) = step (d+1) c (L (.inl i)) := by
  cases active with
  | false => rw [resample_false]
  | true =>
      apply masked_step_occupied
      exact avoid_exposed _ i

lemma mask_false_witness (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (x : Position d)
    (hx : freePairMask d (avoid (fun i => L (.inl i))) x = false) :
    ∃ i : ι, Fin.tail (L (.inl i)) = x := by
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  by_contra h
  have hh : ∀ b : Bool, avoid (fun i => L (.inl i)) (Fin.cons b x) = true := by
    intro b
    simp only [avoid, decide_eq_true_eq]
    intro i hi
    apply h
    exact ⟨i, by rw [hi]; rfl⟩
  simp only [freePairMask, hh, Bool.and_self, Bool.true_eq_false] at hx

lemma resample_obs (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c r : Coins (d+1)) :
    (stepInstrument (d+1) σ).obs e (resample d (sectionFrame e.2) (σ e.1) c r) =
      (stepInstrument (d+1) σ).obs e c := by
  apply Prod.ext
  · apply Subtype.ext; funext i
    exact resample_occupied d (sectionFrame e.2) (σ e.1) c r i
  · cases h : σ e.1 <;> simp only [stepInstrument, h, Bool.false_eq_true, ite_false, ite_true, resample_false]

lemma resample_row (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c c' : Coins (d+1))
    (hh : (stepInstrument (d+1) σ).obs e c = (stepInstrument (d+1) σ).obs e c')
    (r : Coins (d+1)) :
    resample d (sectionFrame e.2) (σ e.1) c r = resample d (sectionFrame e.2) (σ e.1) c' r := by
  cases hs : σ e.1 with
  | false =>
      have hc := congrArg Prod.snd hh
      have hc' : c = c' := by simpa only [stepInstrument, hs, Bool.false_eq_true, ite_false, Option.some.injEq] using hc
      rw [hc']
  | true =>
      funext x
      change (if mask d (sectionFrame e.2) true x then r x else c x) =
        (if mask d (sectionFrame e.2) true x then r x else c' x)
      simp only [mask, Bool.true_and]
      cases hm : freePairMask d (avoid (fun i => sectionFrame e.2 (.inl i))) x with
      | true => rfl
      | false =>
          obtain ⟨i,hi⟩ := mask_false_witness d (sectionFrame e.2) x hm
          have ho := congrFun (congrArg (fun z => z.1.val) hh) i
          have hc := (step_same_at_iff d c c' (sectionFrame e.2 (.inl i))).mp ho
          simpa only [Bool.false_eq_true, ite_false, hi] using hc

lemma resample_kernel (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c : Coins (d+1)) :
    fairMass (fun r : Coins (d+1) => (stepInstrument (d+1) σ).inc e
      (resample d (sectionFrame e.2) (σ e.1) c r)) =
        kernel (stepInstrument (d+1) σ) e ((stepInstrument (d+1) σ).obs e c) := by
  apply resample_conditional _ _ _ (resample_obs d σ e) _ (resample_row d σ e) c
  intro f
  exact mean_maskedCoin _ f

def xorEquiv (d : ℕ) (c : Coins (d+1)) : Equiv.Perm (Coins (d+1)) :=
  Function.Involutive.toPerm (fun r x => c x ^^ r x) (by
    intro r; funext x
    change (c x ^^ (c x ^^ r x)) = r x
    cases c x <;> cases r x <;> rfl)

lemma xor_resample (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) :
    xorCoins d L active c r = resample d L active c (xorEquiv d c r) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  funext x
  change (c x ^^ (if mask d L active x then r x else false)) =
    (if mask d L active x then c x ^^ r x else c x)
  cases mask d L active x <;> simp

lemma mask_frame (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool) :
    mask d L active = mask d (sectionFrame (Split.outside L)) active := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  have hh : (fun i => L (.inl i)) = (fun i => sectionFrame (Split.outside L) (.inl i)) := by
    funext i; exact (sectionFrame_spec (Split.outside L) i).symm
  unfold mask; rw [hh]

lemma xor_kernel (d : ℕ) (σ : ℕ → Bool) (e : ℕ × Outside ι α (Position (d+1)))
    (c : Coins (d+1)) :
    fairMass (fun r : Coins (d+1) => (stepInstrument (d+1) σ).inc e
      (xorCoins d (sectionFrame e.2) (σ e.1) c r)) =
        kernel (stepInstrument (d+1) σ) e ((stepInstrument (d+1) σ).obs e c) := by
  have hh := resample_kernel d σ e c
  refine Eq.trans ?_ hh
  funext g
  rw [fairMass_eq_mean, fairMass_eq_mean]
  have hx := mean_equiv (xorEquiv d c)
    (fun r => if (stepInstrument (d+1) σ).inc e (resample d (sectionFrame e.2) (σ e.1) c r) = g then (1 : ℝ) else 0)
  convert hx using 1
  apply mean_congr; intro r
  rw [xor_resample]
  rfl

end Revealed.Overlay

end

end OAI
