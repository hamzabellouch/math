import OAI.Combinatorics.ContingencyTables.Sampling.ExactExpectedTime
import OAI.Combinatorics.ContingencyTables.Sampling.ExactRarePublicBound

namespace OAI

/-! # The exact public sampler in uniform expected polynomial bit time -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream Turing
open ProfilePrograms DensePrograms Polynomial Algorithms
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] ExactPublicPrefix.program

theorem exact_expected_polynomial : ∃ p : Polynomial ℕ,
    ∀ (_hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
      (_hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*k^8))),
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    (∑' (t : ℕ), (1 - haltMass ExactPublicPrefix.machine (encodeMargins r c) t)) ≤
      ((p.eval (samplingSize n r 0) : ℕ) : ℝ) := by
  obtain ⟨print,hprint⟩ := ExactPrintCost.polynomial_print_bound
  obtain ⟨p,hp⟩ := ExactGatePolynomial.public_bound print
  obtain ⟨q,hq⟩ := exact_public_correction_bound print
  refine ⟨p+11*q,?_⟩
  intro hPL hCheeger m n r c htotal
  let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
  let S := ExactGatePublic.budget r c B B
  let T := ExactPublicCost.budget r c 1 B B+1
  let den : ℝ := (2:ℝ)^correctionPrecision r c
  have hB (X : Table r c) : GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val) ≤ B :=
    (Nat.le_add_right _ _).trans (hprint m n r c X)
  have hL (X : Table r c) : (ExactPublicPrefix.word r c X).length ≤ B :=
    (list_length_le_weight _).trans ((Nat.le_add_left _ _).trans (hprint m n r c X))
  have htail := (ExactExpectedTime.bound r c hPL hCheeger htotal B B hB hL).2
  have hgate : (S:ℝ) ≤ ((p.eval (samplingSize n r 0):ℕ):ℝ) := by exact_mod_cast hp m n r c htotal
  have hT : (T:ℝ) ≤ den*((q.eval (samplingSize n r 0):ℕ):ℝ) := by
    have hn : T ≤ 2^(correctionPrecision r c)*q.eval (samplingSize n r 0) := hq m n r c htotal
    have ht : (T:ℝ) ≤ ((2^(correctionPrecision r c)*q.eval (samplingSize n r 0):ℕ):ℝ) := by
      exact_mod_cast hn
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,den] using ht
  have hrare : (1/den)*T ≤ ((q.eval (samplingSize n r 0):ℕ):ℝ) := by
    have hden : 0 < den := by unfold den; positivity
    have ht : (T:ℝ)/den ≤ ((q.eval (samplingSize n r 0):ℕ):ℝ) :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hT)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using ht
  have he : (fun t => 1-haltMass ExactPublicPrefix.machine (encodeMargins r c) t)=
      PhysicalRetryTail.tail ExactPublicPrefix.program.table
        (ExactPublicPrefix.program.initial (Tape.mk₁ (encodeMargins r c))) := by
    funext t
    exact PhysicalPublicLaw.tail_eq _ _ _
  rw [←he] at htail
  change _ ≤ (S:ℝ)+11*(1/den)*T at htail
  simp only [eval_add,eval_mul,eval_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith

/-- Paper 200-01, main theorem (ii), conditional on the cited finite-box
Prékopa--Leindler and finite-grid Cheeger inputs. The machine is fixed,
including parsing, printing, and the unbiased-bit implementation. -/
theorem exactSampling_conditional
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*k^8))) :
    ExactSamplingStatement := by
  obtain ⟨p,hp⟩ := exact_expected_polynomial
  refine ⟨ExactPublicPrefix.machine,p.eval 1+1,p.natDegree,by omega,?_⟩
  intro m n r c htotal
  dsimp only
  refine ⟨ExactPublicLaw.halted_feasible r c hPL hCheeger htotal,
    ExactPublicLaw.tableMass_limit r c hPL hCheeger htotal,
    ExactPublicLaw.haltMass_limit r c hPL hCheeger htotal,
    ExactExpectedTime.summable r c hPL hCheeger htotal,?_⟩
  have hS : 1 ≤ samplingSize n r 0 := by unfold samplingSize; omega
  have hpoly : p.eval (samplingSize n r 0) ≤ p.eval 1*(samplingSize n r 0)^p.natDegree := by
    simpa only [one_mul,pow_one] using polynomial_scaled_power p 1 (samplingSize n r 0) 1 hS
  have hnat := hpoly.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  have hreal : ((p.eval (samplingSize n r 0):ℕ):ℝ) ≤
      (p.eval 1+1:ℕ)*(samplingSize n r 0:ℝ)^p.natDegree := by exact_mod_cast hnat
  exact (hp hPL hCheeger m n r c htotal).trans hreal

end
end ContingencyTables.SmallGraphProfiles

end OAI
