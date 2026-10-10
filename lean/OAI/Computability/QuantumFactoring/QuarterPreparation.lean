import Mathlib
import OAI.Computability.QuantumFactoring.DyadicCompletion
import OAI.Computability.QuantumFactoring.TransitionEqualization

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

lemma knownProbability_at (n : ℕ) : DyadicAt (n^11) (knownProbability n) := by
  have hd : DyadicAt n (1-1/(2:ℚ)^n) := (DyadicAt.integer n 1).sub ⟨1,by simp⟩
  convert hd.pow (n^10) using 1 <;> first | rfl | ring

namespace Quarter
/-- The second rounding uses EXACTLY J+2, not the transition completion's
slightly finer W+t+2 grid. One surplus fair retention bit is harmless. -/
def retention (n : ℕ) : ℚ := quarterCoeff (n*n) (knownProbability n)
def guessRetention (n : ℕ) : ℚ := (2:ℚ)^(n*n+1)*quarterRemainder (n*n) (knownProbability n)
abbrev D (n : ℕ) : ℕ := Completion.coinBits (n*n) 1 (n^11)
abbrev Raw (α : Type*) (n : ℕ) := Completion.Raw α (n*n) 1 (n^11)
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (n : ℕ) : Raw α n→ℂ :=
  Completion.fresh ψ (n*n) 1 (n^11)

lemma retention_at (n : ℕ) : DyadicAt (D n) (retention n) := by
  apply (show DyadicAt (n*n+2) (retention n) from ⟨_,rfl⟩).mono
  unfold D Completion.coinBits
  omega
lemma guessRetention_at (n : ℕ) : DyadicAt (D n) (guessRetention n) := by
  have hC : DyadicAt (n*n+2) (retention n) := ⟨_,rfl⟩
  have hP := (knownProbability_at n).mul hC
  have hhalf : DyadicAt 1 (1/2) := ⟨1,by norm_num⟩
  have hprod := hP.mul hhalf
  have hprod' : DyadicAt (D n) (knownProbability n*retention n/2) := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using hprod.mono (l:=D n) (by unfold D Completion.coinBits; omega)
  have hquarter : DyadicAt (D n) (1/4) :=
    (show DyadicAt 2 (1/4) from ⟨1,by norm_num⟩).mono (by unfold D Completion.coinBits; omega)
  have h := (hquarter.sub hprod').int_mul (2^(n*n+1))
  simpa only [guessRetention,quarterRemainder,retention,Int.cast_pow,Int.cast_ofNat] using h

def ordinaryPass {α : Type*} {n : ℕ} (success : α→Prop) (r : Raw α n) : Prop :=
  ¬Completion.rare r.1 ∧ (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2)
def guessPass {α : Type*} {n : ℕ} (N : ℕ) (r : Raw α n) : Prop :=
  Completion.rare r.1 ∧ (CorrectEncoding N n (guessWords n r.2.2.1) ∧
    Completion.threshold (guessRetention n) r.2.2.2)
def passed {α : Type*} {n : ℕ} (N : ℕ) (success : α→Prop) (r : Raw α n) : Prop :=
  ordinaryPass success r ∨ guessPass N r

theorem passed_mass {α : Type*} [Fintype α] {N n : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (ψ : α→ℂ) (success : α→Prop) (hψ : ∑ x,Complex.normSq (ψ x)=1)
    (hs : outcomeMass success ψ=(knownProbability n:ℝ)) :
    outcomeMass (passed N success) (fresh ψ n)=1/4 := by
  obtain ⟨hp₀,hp₁⟩ := knownProbability_bounds hn
  obtain ⟨hC₀,hC₁,hG₀,hG₁⟩ := quarter_retention_bounds (n*n) hp₀ hp₁
  have hC := dyadic_fair_threshold (retention_at n) hC₀ hC₁
  have hG := dyadic_fair_threshold (guessRetention_at n) hG₀ (hG₁.le.trans (by norm_num))
  have hr : outcomeMass (fun b : Basis 1 => Completion.rare b) (fairState 1)=1/2 := by
    simpa only [Completion.rare,pow_one] using (fair_value_mass (by norm_num : 0<2^1))
  have hnr : outcomeMass (fun b : Basis 1 => ¬Completion.rare b) (fairState 1)=1/2 := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized 1),hr]
    norm_num
  have ho : outcomeMass (ordinaryPass (n:=n) success) (fresh ψ n)=
      (1/2)*(knownProbability n:ℝ)*(retention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => ¬Completion.rare r.1 ∧
      (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      (fun b => ¬Completion.rare b) (fun r => success r.1 ∧ Completion.threshold (retention n) r.2.2),
      independent_mass ψ (independentState (fairState (n*n)) (fairState (D n)))
      success (fun r => Completion.threshold (retention n) r.2),
      independent_mass_right _ _ _ (fair_normalized (n*n))]
    rw [hnr,hs]
    rw [show outcomeMass (Completion.threshold (D:=D n) (retention n)) (fairState (D n))=
      (retention n:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (n:=n) N) (fresh ψ n)=
      (1/2)*(1/(2:ℝ)^(n*n))*(guessRetention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => Completion.rare r.1 ∧
      (CorrectEncoding N n (guessWords n r.2.2.1) ∧ Completion.threshold (guessRetention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      Completion.rare (fun r => CorrectEncoding N n (guessWords n r.2.1) ∧
        Completion.threshold (guessRetention n) r.2.2),
      independent_mass_right ψ (independentState (fairState (n*n)) (fairState (D n)))
      (fun r => CorrectEncoding N n (guessWords n r.1) ∧ Completion.threshold (guessRetention n) r.2) hψ,
      independent_mass (fairState (n*n)) (fairState (D n))
      (fun x => CorrectEncoding N n (guessWords n x)) (Completion.threshold (guessRetention n)),
      hr,fair_guess_mass hN hb]
    rw [show outcomeMass (Completion.threshold (D:=D n) (guessRetention n)) (fairState (D n))=
      (guessRetention n:ℝ) from hG]
    simp only [one_div,inv_pow]
    ring
  change outcomeMass (fun r => ordinaryPass success r ∨ guessPass N r) (fresh ψ n)=1/4
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have h := congrArg (fun q : ℚ => (q:ℝ)) (quarter_mass (n*n) (knownProbability n))
  push_cast at h
  simpa only [retention,guessRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using h

/-- The flagged output always has the same canonical root encoding. -/
theorem passed_correct {α : Type*} {N n : ℕ} (ordinary : α→Basis (n*n)) (success : α→Prop)
    (hsound : ∀ a,success a → CorrectEncoding N n (guessWords n (ordinary a)))
    (r : Raw α n) (h : passed N success r) :
    CorrectEncoding N n (guessWords n (Completion.output ordinary r)) := by
  rcases h with h | h
  · simpa only [Completion.output,ite_eq_right h.1] using hsound r.2.1 h.2.1
  · simpa only [Completion.output,ite_eq_left h.1] using h.2.1

/-- No probability or canonical factor list occurs in the raw unitary. -/
def program {q : ℕ} (P : List (Instruction q)) (n : ℕ) := Completion.program P (n*n) 1 (n^11)
lemma program_entry {q : ℕ} (P : List (Instruction q)) (n : ℕ) (a : Basis q) (r : Raw (Basis q) n) :
    (programMatrix (program P n)).mulVec
      (basisVector (Completion.layout q (n*n) 1 (n^11) ((fun _ => false),a,(fun _ => false),(fun _ => false))))
      (Completion.layout q (n*n) 1 (n^11) r)=fresh ((programMatrix P).mulVec (basisVector a)) n r :=
  Completion.program_entry P (n*n) 1 (n^11) a r
lemma program_length {q : ℕ} (P : List (Instruction q)) (n : ℕ) :
    (program P n).length=P.length+1+n*n+D n := Completion.program_length P (n*n) 1 (n^11)

end Quarter
end ExactQuantumFactoring


end

end OAI
