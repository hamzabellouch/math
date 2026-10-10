import OAI.NumberTheory.TotientAsymptotic.FordTerminalConditions
import OAI.NumberTheory.TotientAsymptotic.TerminalLogBudget
import OAI.NumberTheory.TotientAsymptotic.SmoothTerminalBound

namespace OAI

/-! The terminal mass bounds for the actual Ford state families. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_cutoff_two_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) {k : ℕ} (hk : k ≤ b) : 2 ≤ Y k := by
  have hs : Real.exp (Real.exp 1) ≤ S := hp.2.2.1
  have h₁ := Real.add_one_le_exp (1:ℝ)
  have h₂ := Real.add_one_le_exp (Real.exp 1)
  linarith [ford_cutoff_ge_S hp hk]

lemma ford_cutoff_B_one_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) {k : ℕ} (hk : k ≤ b) : 1 ≤ B (Y k) := by
  have hS := ford_scale_bounds hp
  exact hS.2.trans (Real.log_le_log (Real.log_pos hS.1)
    (Real.log_le_log (by linarith) (ford_cutoff_ge_S hp hk)))

theorem ford_terminal_mass : ∃ C : ℝ,0 < C ∧
    ∀ (b D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),2 ≤ b →
    FordComparisonParameters b y S D r Y U →
    ∀ T : Finset (ShiftedPair b),(∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    fordStateMass T Y b ≤ C*(b+1:ℝ)^D.primeFactorsList.length*
      (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1) := by
  classical
  obtain ⟨C,hC,hm⟩ := mertensProductInput
  refine ⟨C,hC,?_⟩
  intro b D r y S Y U hb hp T hT
  have hY := ford_cutoff_two_le hp (k:=b) le_rfl
  have hY1 : 1 < Y b := by linarith
  have hN : 2 ≤ ⌊Y b⌋₊ := Nat.le_floor (by simpa using hY)
  have hD : 0 < D := by rcases hp with ⟨_,_,_,_,_,_,_,hD,_,_,_,_⟩; omega
  let Q := T.image (fun t => fordFactorState t (Y b))
  have hQ : ∀ q ∈ Q,0 < factorProduct q ∧
      D*factorProduct q=q.remainder*(∏ j,q.right j) ∧
      largestPrimeFactor (factorProduct q) ≤ ⌊Y b⌋₊ ∧
      ((factorProduct q).primeFactorsList.length:ℝ) ≤ 4*(b:ℝ)*B (Y b) := by
    intro q hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨Finset.prod_pos (fun j _ => partBelow_pos _ _),
      ford_terminal_equation hp (hT t ht),Nat.le_floor (ford_terminal_largest hp),
      ford_terminal_omega hp (hT t ht)⟩
  have hmass := terminal_state_mass (by omega) hD Q hQ
  have hlog : Real.log (⌊Y b⌋₊:ℝ) ≤ Real.log (Y b) :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊Y b⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hEuler : primeEulerProduct ⌊Y b⌋₊ ≤ C*Real.log (Y b) :=
    (hm _ hN).trans (mul_le_mul_of_nonneg_left hlog hC.le)
  have ht := terminal_allocation_log_budget hb hY1
    (by linarith [ford_cutoff_B_one_le hp (k:=b) le_rfl])
  calc
    _ ≤ (b+1:ℝ)^D.primeFactorsList.length*
        ((b:ℝ)*(b+1))^(4*(b:ℝ)*B (Y b))*primeEulerProduct ⌊Y b⌋₊ := hmass
    _ ≤ (b+1:ℝ)^D.primeFactorsList.length*
        ((b:ℝ)*(b+1))^(4*(b:ℝ)*B (Y b))*(C*Real.log (Y b)) :=
      mul_le_mul_of_nonneg_left hEuler (by positivity)
    _ = C*(b+1:ℝ)^D.primeFactorsList.length*
        (((b:ℝ)*(b+1))^(4*(b:ℝ)*B (Y b))*Real.log (Y b)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)

def oneStateTriple (q : ShiftedPair 1) : SmoothTerminalTriple := (q.left 0,q.right 0,q.remainder)

lemma oneStateTriple_injective : Function.Injective oneStateTriple := by
  intro q t h
  have hl : q.left=t.left := by
    funext j
    fin_cases j
    exact congrArg Prod.fst h
  have hr : q.right=t.right := by
    funext j
    fin_cases j
    exact congrArg (fun z : SmoothTerminalTriple => z.2.1) h
  have he : q.remainder=t.remainder := congrArg (fun z : SmoothTerminalTriple => z.2.2) h
  cases q; cases t; cases hl; cases hr; cases he; rfl

theorem ford_terminal_mass_one : ∃ C : ℝ,0 < C ∧
    ∀ (D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),
    FordComparisonParameters 1 y S D r Y U →
    ∀ T : Finset (ShiftedPair 1),(∀ t ∈ T,FordComparisonConditions 1 y S D r Y U t) →
    fordStateMass T Y 1 ≤ C*(2:ℝ)^D.primeFactorsList.length*(Real.log (Y 1))^2 := by
  classical
  obtain ⟨C,hC,hm⟩ := smooth_terminal_log_bound
  refine ⟨C,hC,?_⟩
  intro D r y S Y U hp T hT
  have hY := ford_cutoff_two_le hp (k:=1) le_rfl
  have hD : 0 < D := by rcases hp with ⟨_,_,_,_,_,_,_,hD,_,_,_,_⟩; omega
  have hN : 2 ≤ ⌊Y 1⌋₊ := Nat.le_floor (by simpa using hY)
  let Q := T.image (fun t => fordFactorState t (Y 1))
  let E := Q.image oneStateTriple
  have hE : ∀ z ∈ E,TerminalConditions D ⌊Y 1⌋₊ z := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    have he := ford_terminal_equation hp (hT t ht)
    have hl := ford_terminal_largest (t:=t) hp
    simp only [factorProduct,Fin.prod_univ_one] at he hl
    refine ⟨partBelow_pos _ _,?_,Nat.le_floor hl⟩
    simpa only [oneStateTriple,terminalFirst,terminalMiddle,terminalLast,mul_comm] using he
  have hmass := hm D ⌊Y 1⌋₊ hD (Nat.le_floor (by simpa using hY)) E hE
  have heq : (∑ z ∈ E,(terminalFirst z:ℝ)⁻¹)=fordStateMass T Y 1 := by
    rw [Finset.sum_image (fun q _ t _ h => oneStateTriple_injective h)]
    simp only [oneStateTriple,terminalFirst,factorProduct,Fin.prod_univ_one,fordStateMass,Q]
  rw [heq] at hmass
  have hlog : Real.log (⌊Y 1⌋₊:ℝ) ≤ Real.log (Y 1) :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊Y 1⌋₊ by omega))
      (Nat.floor_le (by linarith))
  have hlog0 : 0 ≤ Real.log (⌊Y 1⌋₊:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ⌊Y 1⌋₊ by omega))
  exact hmass.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) (by positivity))

end TotientAsymptotic

end

end OAI
