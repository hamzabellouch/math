import OAI.Dynamics.ConditionalShuffle.InstrumentMap

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Scheduled
open Thorp Thorp.Conditional Thorp.Conditional.Hybrid Revealed.Split Revealed.Instrument Revealed.Disintegration
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

lemma observed_same (d t τ : ℕ) (σ ρ : ℕ → Bool)
    (h : ∀ i : Fin t, σ (τ+i.val) = ρ i.val)
    (e : Outside ι α (Position d)) (ω : History d t) :
    observed (stepInstrument d σ) (τ,e) t ω = observed (stepInstrument d ρ) (0,e) t ω := by
  funext i
  apply Prod.ext
  · exact (congrFun (observed_outside d σ τ e t ω) i).trans
      (congrFun (observed_outside d ρ 0 e t ω) i).symm
  · have h₁ := congrFun (observed_public d σ τ e t ω) i
    have h₂ := congrFun (observed_public d ρ 0 e t ω) i
    rw [h₁, h₂]
    simp only [publicHistory, Nat.zero_add, h i]

lemma interval_congr (d t : ℕ) (σ ρ : ℕ → Bool)
    (h : ∀ i : Fin t, σ i.val = ρ i.val) :
    (interval (ι:=ι) (α:=α) d t σ) = interval d t ρ := by
  apply Data.ext
  · funext e ω
    exact observed_same d t 0 σ ρ (by simpa only [Nat.zero_add] using h) e ω
  · funext e ω
    exact (group_eq d σ 0 e t ω).trans (group_eq d ρ 0 e t ω).symm
  · funext e p
    exact (base_outside d σ 0 e t p).trans (base_outside d ρ 0 e t p).symm

lemma distance_schedule_le (d t : ℕ) (σ ρ : ℕ → Bool)
    (h : ∀ i : Fin t, ρ i.val = true → σ i.val = true)
    (e : Outside ι α (Position d)) :
    Instrument.distance (stepInstrument d σ) (0,e) t ≤
      Instrument.distance (stepInstrument d ρ) (0,e) t := by
  let f : (Fin t → Symbol ι α d) → (Fin t → Symbol ι α d) :=
    fun p i => ((p i).1, if σ i.val then none else (p i).2)
  have hob (ω : History d t) :
      f (observed (stepInstrument d ρ) (0,e) t ω) = observed (stepInstrument d σ) (0,e) t ω := by
    funext i
    apply Prod.ext
    · exact (congrFun (observed_outside d ρ 0 e t ω) i).trans
        (congrFun (observed_outside d σ 0 e t ω) i).symm
    · have h₁ := congrFun (observed_public d ρ 0 e t ω) i
      have h₂ := congrFun (observed_public d σ 0 e t ω) i
      change (if σ i.val then none else (observed (stepInstrument d ρ) (0,e) t ω i).2) = _
      rw [h₁,h₂]
      simp only [publicHistory, Nat.zero_add]
      cases hσ : σ i.val <;> cases hρ : ρ i.val <;> simp_all
  have hg (ω : History d t) :
      groupRun (stepInstrument d ρ) (0,e) t ω = groupRun (stepInstrument d σ) (0,e) t ω :=
    (group_eq d ρ 0 e t ω).trans (group_eq d σ 0 e t ω).symm
  have hh := average_tv_transport
    (observed (stepInstrument d ρ) (0,e) t) (groupRun (stepInstrument d ρ) (0,e) t)
    f (fun _ => Equiv.refl (Equiv.Perm α))
  simp only [Equiv.refl_apply, hob, hg] at hh
  simpa only [distance_disintegration, pathJoint, hg] using hh

def clockInterval (d t : ℕ) (σ : ℕ → Bool) :
    Data (ℕ × Outside ι α (Position d)) (Fin t → Symbol ι α d) (Equiv.Perm α) (History d t) where
  obs e c := (interval d t σ).obs e.2 c
  inc e c := (interval d t σ).inc e.2 c
  next e p := (e.1+1, (interval d t σ).next e.2 p)

lemma distance_periodic (d t : ℕ) (σ : ℕ → Bool)
    (h : ∀ k s, σ (t*k+s) = σ s) (e : Outside ι α (Position d)) (n : ℕ) :
    Instrument.distance (stepInstrument d σ) (0,e) (t*n) =
      Instrument.distance (interval d t σ) e n := by
  let I := clockInterval (ι:=ι) (α:=α) d t σ
  have h₁ := map_distance I (interval d t σ) Prod.snd
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (0,e) n
  have h₂ := map_distance I (block (stepInstrument d σ) t)
    (fun e : ℕ × Outside ι α (Position d) => (t*e.1,e.2))
    (fun e c => observed_same d t (t*e.1) σ σ (fun i => h e.1 i.val) e.2 c)
    (fun e c => (group_eq d σ (t*e.1) e.2 t c).trans (group_eq d σ 0 e.2 t c).symm)
    (by
      intro e p
      apply Prod.ext
      · change (base (stepInstrument d σ) (t*e.1,e.2) t p).1 = t*(e.1+1)
        rw [base_clock]; ring
      · change (base (stepInstrument d σ) (t*e.1,e.2) t p).2 =
          (base (stepInstrument d σ) (0,e.2) t p).2
        rw [base_outside, base_outside]) (0,e) n
  simp only [Nat.mul_zero, distance_block] at h₂
  exact h₂.trans h₁.symm

end Revealed.Scheduled

end

end OAI
