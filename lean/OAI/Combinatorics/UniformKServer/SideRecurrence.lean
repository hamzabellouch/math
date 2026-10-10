import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveSide

namespace OAI

                                     
section

/-! Persistent causal selection of the two actual side minimizers. Empty side
 domains and D=0 use the same compact update, with the source's free deletion. -/
noncomputable section
namespace UniformKServer.SideRecurrence
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def StepSpec (p q : Config ι) (Bstar Bnew old w v : ι → ℝ) (D S : ℝ) : Prop :=
  DomainTransport.domain q.active 11 w ∧ DomainTransport.domain q.active 11 v ∧
  (∀ i, D*w i ≤ (q.b+theta q i)*Bnew i) ∧
  (S ≤ 2*D → ∀ i, q.b*Bnew i-theta q i*offset q i*D ≤ D*w i) ∧
  (∀ i, D*v i ≤ (p.b+theta p i)*Bstar i) ∧
  D*SideTracker.movement w old ≤ potential p Bstar D old-potential q Bnew D w+
    (potential q Bstar D v-potential p Bstar D v)+slope q*(∑ i, |Bnew i-Bstar i|)

def chooseStep (p q : Config ι) (Bstar Bnew old : ι → ℝ) (D S : ℝ) : (ι → ℝ) × (ι → ℝ) :=
  if h : ∃ wv : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old wv.1 wv.2 D S
    then h.choose else (fun _ => 0,fun _ => 0)

theorem zero_state (p : Config ι) : DomainTransport.domain p.active 11 (fun _ => 0) := by
  exact ⟨fun _ => le_rfl,fun _ _ => rfl,by simp⟩

theorem chooseStep_spec {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew old : ι → ℝ) (D S : ℝ) (hD : 0 ≤ D)
    (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i) (hS : (∑ i, Bnew i) ≤ S)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (hold : DomainTransport.domain p.active 11 old) :
    StepSpec p q Bstar Bnew old (chooseStep p q Bstar Bnew old D S).1
      (chooseStep p q Bstar Bnew old D S).2 D S := by
  have hex : ∃ wv : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old wv.1 wv.2 D S := by
    obtain ⟨w,v,h⟩ := AdaptiveSide.step hp hq Bstar Bnew old D S hD hB hBn hS hpB hqB hqN hold
    exact ⟨(w,v),h⟩
  unfold chooseStep
  rw [dite_eq_left hex]
  exact hex.choose_spec

def trajectory (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 0
  | t+1 => (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1))
      (trajectory p Bstar B D S t) (D (t+1)) (S (t+1))).1

def prepared (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) (t : ℕ) : ι → ℝ :=
  (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1))
      (trajectory p Bstar B D S t) (D (t+1)) (S (t+1))).2

def InputValid (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) : Prop :=
  (∀ t, valid (p t)) ∧ (∀ t, 0 ≤ D t) ∧ (∀ t i, 0 ≤ Bstar t i) ∧ (∀ t i, 0 ≤ B t i) ∧
  (∀ t, (∑ i, B t i) ≤ S t) ∧
  (∀ t, DomainTransport.Supported (p t).active (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (p (t+1)).active (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (p t).active (B t))

theorem trajectory_state {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ} {D S : ℕ → ℝ}
    (h : InputValid p Bstar B D S) : ∀ t,
    DomainTransport.domain (p t).active 11 (trajectory p Bstar B D S t) := by
  rcases h with ⟨hp,hD,hB,hBn,hS,hpB,hqB,hqN⟩
  intro t
  induction t with
  | zero => exact zero_state _
  | succ t ih => exact (chooseStep_spec (hp t) (hp (t+1)) _ _ _ _ _ (hD (t+1))
      (hB t) (hBn (t+1)) (hS (t+1)) (hpB t) (hqB t) (hqN (t+1)) ih).1

theorem trajectory_step {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ} {D S : ℕ → ℝ}
    (h : InputValid p Bstar B D S) (t : ℕ) :
    StepSpec (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B D S t)
      (trajectory p Bstar B D S (t+1)) (prepared p Bstar B D S t) (D (t+1)) (S (t+1)) := by
  have hstate := trajectory_state h t
  obtain ⟨hp,hD,hB,hBn,hS,hpB,hqB,hqN⟩ := h
  exact chooseStep_spec (hp t) (hp (t+1)) _ _ _ _ _ (hD (t+1))
    (hB t) (hBn (t+1)) (hS (t+1)) (hpB t) (hqB t) (hqN (t+1)) hstate

theorem causal_through (p q : ℕ → Config ι) (F G B E : ℕ → ι → ℝ)
    (D S D' S' : ℕ → ℝ) (n : ℕ) (hp : ∀ t, t ≤ n → p t=q t)
    (hF : ∀ t, t < n → F t=G t) (hB : ∀ t, t ≤ n → B t=E t)
    (hD : ∀ t, t ≤ n → D t=D' t) (hS : ∀ t, t ≤ n → S t=S' t) :
    trajectory p F B D S n=trajectory q G E D' S' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun t ht => hp t (ht.trans (Nat.le_succ n)))
      (fun t ht => hF t (ht.trans (Nat.lt_succ_self n)))
      (fun t ht => hB t (ht.trans (Nat.le_succ n)))
      (fun t ht => hD t (ht.trans (Nat.le_succ n)))
      (fun t ht => hS t (ht.trans (Nat.le_succ n)))
    simp only [trajectory,hp n (Nat.le_succ n),hp (n+1) le_rfl,
      hF n (Nat.lt_succ_self n),hB (n+1) le_rfl,hD (n+1) le_rfl,hS (n+1) le_rfl,he]

end UniformKServer.SideRecurrence

end


end

end OAI
