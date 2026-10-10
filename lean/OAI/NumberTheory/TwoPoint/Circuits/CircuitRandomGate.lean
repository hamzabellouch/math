import OAI.NumberTheory.TwoPoint.Circuits.CircuitIsolation

namespace OAI

/-! Polynomial gate replacement. A sampled subset contributes a linear
factor that is one on an all-true input and zero when the subset contains
exactly one false input. Repetition is a product of these factors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {n : ℕ}

lemma WalshDegreeLE.prod {ι : Type*} (I : Finset ι) (F : ι → BooleanCube n → ℝ)
    (d : ℕ) (hF : ∀ i ∈ I, WalshDegreeLE (F i) d) :
    WalshDegreeLE (fun x => ∏ i ∈ I, F i x) (d * I.card) := by
  induction I using Finset.induction_on with
  | empty => simpa using WalshDegreeLE.const (n := n) 1 0
  | @insert i I hi ih =>
    have hFi := hF i (mem_insert_self i I)
    have hI := ih (fun j hj => hF j (mem_insert_of_mem hj))
    have hh := hFi.mul hI
    have heq : (fun x => ∏ j ∈ insert i I, F j x) =
        fun x => F i x * ∏ j ∈ I, F j x := by
      funext x
      exact prod_insert hi
    rw [heq]
    convert hh using 1
    simp only [card_insert_of_notMem hi]
    ring

noncomputable def andGateFactor {k : ℕ} (S : Finset (Fin k)) (u : Fin k → ℝ) : ℝ :=
  1 - ∑ i ∈ S, (1 - u i)

noncomputable def andGatePolynomial {k r : ℕ}
    (S : Fin r → Finset (Fin k)) (u : Fin k → ℝ) : ℝ :=
  ∏ j, andGateFactor (S j) u

lemma WalshDegreeLE.andGateFactor {k : ℕ} (S : Finset (Fin k))
    (P : Fin k → BooleanCube n → ℝ) (d : ℕ)
    (hP : ∀ i ∈ S, WalshDegreeLE (P i) d) :
    WalshDegreeLE (fun x => TwoPointCorrelations.andGateFactor S (fun i => P i x)) d := by
  have hsum := WalshDegreeLE.sum S (fun i x => 1 - P i x)
    (fun i hi => (WalshDegreeLE.const (n := n) 1 d).sub (hP i hi))
  exact (WalshDegreeLE.const (n := n) 1 d).sub hsum

lemma WalshDegreeLE.andGatePolynomial {k r : ℕ} (S : Fin r → Finset (Fin k))
    (P : Fin k → BooleanCube n → ℝ) (d : ℕ)
    (hP : ∀ i, WalshDegreeLE (P i) d) :
    WalshDegreeLE (fun x => TwoPointCorrelations.andGatePolynomial S (fun i => P i x))
      (d * r) := by
  have hh := WalshDegreeLE.prod univ
    (fun j x => TwoPointCorrelations.andGateFactor (S j) (fun i => P i x)) d
      (fun j _ => WalshDegreeLE.andGateFactor (S j) P d (fun i _ => hP i))
  change WalshDegreeLE (fun x => ∏ j : Fin r,
    TwoPointCorrelations.andGateFactor (S j) (fun i => P i x)) (d * r)
  simpa only [card_univ, Fintype.card_fin] using hh

lemma andGateFactor_all_true {k : ℕ} (S : Finset (Fin k))
    (b : Fin k → Bool) (hb : ∀ i ∈ S, b i = true) :
    andGateFactor S (fun i => if b i then 1 else 0) = 1 := by
  unfold andGateFactor
  have hz : (∑ i ∈ S, (1 - (if b i then (1 : ℝ) else 0))) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [hb i hi]
  rw [hz, sub_zero]

lemma andGateFactor_one_false {k : ℕ} (S : Finset (Fin k))
    (b : Fin k → Bool) (hb : (S.filter (fun i => b i = false)).card = 1) :
    andGateFactor S (fun i => if b i then 1 else 0) = 0 := by
  unfold andGateFactor
  have heq : (∑ i ∈ S, (1 - (if b i then (1 : ℝ) else 0))) =
      ((S.filter (fun i => b i = false)).card : ℝ) := by
    calc
      _ = ∑ i ∈ S, (if b i = false then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro i _
        cases b i <;> norm_num
      _ = _ := by simp
  rw [heq, hb]
  norm_num

lemma andGatePolynomial_all_true {k r : ℕ} (S : Fin r → Finset (Fin k))
    (b : Fin k → Bool) (hb : ∀ i, b i = true) :
    andGatePolynomial S (fun i => if b i then 1 else 0) = 1 := by
  unfold andGatePolynomial
  have hf : ∀ j, andGateFactor (S j) (fun i => if b i then 1 else 0) = 1 :=
    fun j => andGateFactor_all_true (S j) b (fun i _ => hb i)
  simp only [hf, prod_const_one]

lemma andGatePolynomial_isolated_false {k r : ℕ} (S : Fin r → Finset (Fin k))
    (b : Fin k → Bool) (hb : ∃ j, ((S j).filter (fun i => b i = false)).card = 1) :
    andGatePolynomial S (fun i => if b i then 1 else 0) = 0 := by
  obtain ⟨j, hj⟩ := hb
  unfold andGatePolynomial
  exact prod_eq_zero (mem_univ j) (andGateFactor_one_false (S j) b hj)

end TwoPointCorrelations

end OAI
