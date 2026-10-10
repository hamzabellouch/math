import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaEmpty

namespace OAI

                                      
section

/-! A single deterministic selection of the two proven minimizations. This
 supplies causal states, rather than postulating a trajectory satisfying the
 desired movement bound. The fallback branch is never used on valid input. -/
noncomputable section
namespace UniformKServer.AlphaRecurrence
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

def StepSpec (p q : Config ι) (Bstar Bnew old a b : ι → ℝ) : Prop :=
  state q a ∧ state q b ∧
  (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
  (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
  (∑ j, Bnew j)*SimplexTracker.movement a old ≤
    potential p Bstar old-potential q Bnew a+
    (potential q Bstar b-potential p Bstar b)+
    15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i))

def initial (p : Config ι) : ι → ℝ :=
  if h : ∃ a, state p a then h.choose else fun _ => 0

def chooseStep (p q : Config ι) (Bstar Bnew old : ι → ℝ) : (ι → ℝ) × (ι → ℝ) :=
  if h : ∃ ab : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old ab.1 ab.2
    then h.choose else (fun _ => 0,fun _ => 0)

theorem initial_spec {p : Config ι} (hp : valid p) : state p (initial p) := by
  unfold initial
  rw [dite_eq_left (exists_state hp)]
  exact (exists_state hp).choose_spec

theorem chooseStep_spec {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew old : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported (active p) Bstar)
    (hqB : DomainTransport.Supported (active q) Bstar)
    (hqN : DomainTransport.Supported (active q) Bnew) (hold : state p old) :
    StepSpec p q Bstar Bnew old (chooseStep p q Bstar Bnew old).1
      (chooseStep p q Bstar Bnew old).2 := by
  have hex : ∃ ab : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old ab.1 ab.2 := by
    obtain ⟨a,b,h⟩ := AlphaEmpty.step hp hq Bstar Bnew old hB hBn hST hpB hqB hqN hold
    exact ⟨(a,b),h⟩
  unfold chooseStep
  rw [dite_eq_left hex]
  exact hex.choose_spec

def trajectory (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => initial (p 0)
  | t+1 => (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)).1

def prepared (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)).2

def InputValid (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) : Prop :=
  (∀ t, valid (p t)) ∧ (∀ t i, 0 ≤ Bstar t i) ∧ (∀ t i, 0 ≤ B t i) ∧
  (∀ t, (∑ i, Bstar t i) ≤ ∑ i, B (t+1) i) ∧
  (∀ t, DomainTransport.Supported (active (p t)) (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (active (p (t+1))) (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (active (p t)) (B t))

theorem trajectory_state {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ}
    (h : InputValid p Bstar B) : ∀ t, state (p t) (trajectory p Bstar B t) := by
  intro t
  induction t with
  | zero => exact initial_spec (h.1 0)
  | succ t ih => exact (chooseStep_spec (h.1 t) (h.1 (t+1)) _ _ _ (h.2.1 t)
      (h.2.2.1 (t+1)) (h.2.2.2.1 t) (h.2.2.2.2.1 t) (h.2.2.2.2.2.1 t)
      (h.2.2.2.2.2.2 (t+1)) ih).1

theorem trajectory_step {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ}
    (h : InputValid p Bstar B) (t : ℕ) :
    StepSpec (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)
      (trajectory p Bstar B (t+1)) (prepared p Bstar B t) :=
  chooseStep_spec (h.1 t) (h.1 (t+1)) _ _ _ (h.2.1 t)
    (h.2.2.1 (t+1)) (h.2.2.2.1 t) (h.2.2.2.2.1 t) (h.2.2.2.2.2.1 t)
    (h.2.2.2.2.2.2 (t+1)) (trajectory_state h t)

variable {Ω : Type*}
/-- Prefix equality suffices for output equality; choices cannot inspect any
 later input. This directly gives measurability in every finite reveal law. -/
theorem causal_through (p q : ℕ → Config ι) (S T B D : ℕ → ι → ℝ) (n : ℕ)
    (hp : ∀ t, t ≤ n → p t=q t) (hS : ∀ t, t < n → S t=T t)
    (hB : ∀ t, t ≤ n → B t=D t) :
    trajectory p S B n=trajectory q T D n := by
  induction n with
  | zero => simp only [trajectory,hp 0 le_rfl]
  | succ n ih =>
    have he := ih (fun t ht => hp t (ht.trans (Nat.le_succ n)))
      (fun t ht => hS t (ht.trans (Nat.lt_succ_self n)))
      (fun t ht => hB t (ht.trans (Nat.le_succ n)))
    simp only [trajectory,hp n (Nat.le_succ n),hp (n+1) le_rfl,
      hS n (Nat.lt_succ_self n),hB (n+1) le_rfl,he]

end UniformKServer.AlphaRecurrence

end


end

end OAI
