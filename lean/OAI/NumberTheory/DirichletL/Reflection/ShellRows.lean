import OAI.NumberTheory.DirichletL.Reflection.ShellDomains

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalDyadicRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    literalDyadicBlock (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem literalDyadicRow_eq_physical (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw=
      weightedFinitePhysicalKernelRow F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X r aw (fun _ _ => 1) := by
  unfold literalDyadicRow weightedFinitePhysicalKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type,mul_one]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [literalDyadicBlock_eq_filtered_source F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  simp only [Finset.mul_sum]
end
end SevenEighths.InverseReflectedPhase

end OAI
