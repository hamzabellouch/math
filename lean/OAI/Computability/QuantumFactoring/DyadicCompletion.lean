import Mathlib
import OAI.Computability.QuantumFactoring.RepeatedTrials
import OAI.Computability.QuantumFactoring.TrialRawPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

namespace Completion

def coeff (W t : ℕ) (s z : ℚ) : ℚ := completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s)
def guessRetention (W t : ℕ) (s z : ℚ) : ℚ :=
  completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)
def coinBits (W t d : ℕ) : ℕ := (W+t+2)+t+d

lemma coeff_at (W t d : ℕ) (s z : ℚ) : DyadicAt (coinBits W t d) (coeff W t s z) := by
  apply (show DyadicAt (W+t+2) (coeff W t s z) from ⟨_,rfl⟩).mono
  unfold coinBits
  omega

lemma guess_at {W t d j : ℕ} {s z : ℚ} (hs : DyadicAt d s) (hz : DyadicAt j z)
    (hj : j≤coinBits W t d) : DyadicAt (coinBits W t d) (guessRetention W t s z) := by
  have hδ : DyadicAt t (1/(2:ℚ)^t) := ⟨1,by simp⟩
  have hA : DyadicAt (t+d) ((1-1/(2:ℚ)^t)*s) := by
    simpa using ((DyadicAt.integer t 1).sub hδ).mul hs
  have hC : DyadicAt (W+t+2) (coeff W t s z) := ⟨_,rfl⟩
  have hCA : DyadicAt (coinBits W t d) (coeff W t s z*((1-1/(2:ℚ)^t)*s)) := by
    simpa only [coinBits,Nat.add_assoc] using hC.mul hA
  have hR := (hz.mono hj).sub hCA
  have hG := hR.int_mul (2^(W+t))
  convert hG using 1
  push_cast
  unfold guessRetention completionRemainder coeff
  rw [pow_add]
  field_simp

abbrev Raw (α : Type*) (W t d : ℕ) := Basis t × (α × (Basis W × Basis (coinBits W t d)))
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (W t d : ℕ) : Raw α W t d→ℂ :=
  independentState (fairState t) (independentState ψ
    (independentState (fairState W) (fairState (coinBits W t d))))

def rare {t : ℕ} (b : Basis t) : Prop := (bitsValue b).toNat=0
instance {t : ℕ} (b : Basis t) : Decidable (rare b) :=
  inferInstanceAs (Decidable ((bitsValue b).toNat=0))

def threshold {D : ℕ} (p : ℚ) (b : Basis D) : Prop :=
  (bitsValue b).toNat<(Int.floor (p*(2:ℚ)^D)).toNat

def output {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (r : Raw α W t d) : Basis W :=
  if rare r.1 then r.2.2.1 else ordinary r.2.1

def ordinaryPass {α : Type*} {W t d : ℕ} (good : α→Prop) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)
def guessPass {α : Type*} {W t d : ℕ} (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)
def passed {α : Type*} {W t d : ℕ} (good : α→Prop) (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ guessPass y₀ s z r

lemma fair_eq_mass (W : ℕ) (y₀ : Basis W) :
    outcomeMass (fun y => y=y₀) (fairState W)=1/(2:ℝ)^W := by
  classical
  simp only [outcomeMass,Finset.sum_ite_eq',Finset.mem_univ,ite_true,fairState_mass,one_div,inv_pow]

lemma fresh_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (W t d : ℕ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) : ∑ x,Complex.normSq (fresh ψ W t d x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState W)
    (fun _ => fairState (coinBits W t d)) (fair_normalized W) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized ψ
    (fun _ => independentState (fairState W) (fairState (coinBits W t d))) hψ (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState t)
    (fun _ => independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
    (fair_normalized t) (fun _ => h₂)

/-- Actual fresh registers do NOT depend on s, goodness or the canonical output.
Those values are used only by the later classical test on the retained record. -/
theorem passed_mass {α : Type*} [Fintype α] {W t d j : ℕ}
    (ψ : α→ℂ) (good : α→Prop) (y₀ : Basis W) (s z : ℚ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) (hgood : outcomeMass good ψ=(s:ℝ))
    (hsd : DyadicAt d s) (hzd : DyadicAt j z) (hj : j≤coinBits W t d)
    (hs₀ : 0<s) (hs₁ : s≤1) (ht : 0<t) (hz : 0<z)
    (hzA : z≤(1-1/(2:ℚ)^t)*s) :
    outcomeMass (passed good y₀ s z) (fresh ψ W t d)=(z:ℝ) := by
  have hb := completion_retention_bounds W t hs₀ hs₁ ht hz hzA
  have hC := dyadic_fair_threshold (coeff_at W t d s z) hb.1 hb.2.1
  have hG := dyadic_fair_threshold (guess_at hsd hzd hj) hb.2.2.1 (hb.2.2.2.le.trans (by norm_num))
  have hr : outcomeMass (rare (t:=t)) (fairState t)=1/(2:ℝ)^t :=
    fair_value_mass (by positivity : 0<2^t)
  have hnr : outcomeMass (fun b : Basis t => ¬rare b) (fairState t)=1-1/(2:ℝ)^t := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized t),hr]
  have ho : outcomeMass (ordinaryPass (W:=W) (t:=t) (d:=d) good s z) (fresh ψ W t d)=
      (1-1/(2:ℝ)^t)*(s:ℝ)*(coeff W t s z:ℝ) := by
    rw [show ordinaryPass (W:=W) (t:=t) (d:=d) good s z =
      (fun r : Raw α W t d => ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      (fun b => ¬rare b) (fun r => good r.1 ∧ threshold (coeff W t s z) r.2.2),
      independent_mass ψ (independentState (fairState W) (fairState (coinBits W t d)))
      good (fun r => threshold (coeff W t s z) r.2),
      independent_mass_right _ _ _ (fair_normalized W)]
    rw [hnr,hgood]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (coeff W t s z))
      (fairState _)= (coeff W t s z:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (t:=t) (d:=d) y₀ s z) (fresh ψ W t d)=
      (1/(2:ℝ)^t)*(1/(2:ℝ)^W)*(guessRetention W t s z:ℝ) := by
    rw [show guessPass (t:=t) (d:=d) y₀ s z =
      (fun r : Raw α W t d => rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      rare (fun r => r.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2),
      independent_mass_right ψ (independentState (fairState W) (fairState (coinBits W t d)))
        (fun r => r.1=y₀ ∧ threshold (guessRetention W t s z) r.2) hψ,
      independent_mass (fairState W) (fairState (coinBits W t d)) (fun y => y=y₀)
        (threshold (guessRetention W t s z)),fair_eq_mass,hr]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (guessRetention W t s z))
      (fairState _)= (guessRetention W t s z:ℝ) from hG]
    ring
  change outcomeMass (fun r => ordinaryPass good s z r ∨ guessPass y₀ s z r)
    (fresh ψ W t d)=(z:ℝ)
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have he := congrArg (fun q : ℚ => (q:ℝ)) (completion_mass W t s z)
  push_cast at he
  simpa [coeff,guessRetention] using he

lemma passed_good {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (P : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hy : P y₀) (r : Raw α W t d)
    (h : passed (P∘ordinary) y₀ s z r) : P (output ordinary r) := by
  rcases h with h | h
  · simpa only [output,ite_eq_right h.1,Function.comp_def] using h.2.1
  · simpa only [output,ite_eq_left h.1,h.2.1] using hy

/-- Literal fixed-gate program for the raw extended record; no oracle for the
future data, success probability, or distinguished guess occurs in its code. -/
def program {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    List (Instruction (t+(q+(W+coinBits W t d)))) :=
  parallelProgram (hadamardPrefix t t le_rfl) (parallelProgram P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix (coinBits W t d) (coinBits W t d) le_rfl)))
def layout (q W t d : ℕ) : Raw (Basis q) W t d ≃ Basis (t+(q+(W+coinBits W t d))) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (Equiv.refl _)))
lemma program_entry {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) (a : Basis q)
    (r : Raw (Basis q) W t d) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _ => false),a,(fun _ => false),(fun _ => false))))
      (layout q W t d r)=fresh ((programMatrix P).mulVec (basisVector a)) W t d r := by
  simp only [program,layout,productLayout_apply,Equiv.refl_apply,parallelProgram_entry,hadamards_zero]
  rfl
lemma program_length {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    (program P W t d).length=P.length+t+W+coinBits W t d := by
  simp only [program,parallelProgram_length,hadamardPrefix_length]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI
