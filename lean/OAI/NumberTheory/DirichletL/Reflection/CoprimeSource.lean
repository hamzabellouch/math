import OAI.NumberTheory.DirichletL.Reflection.KernelActualSource
import OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

abbrev CoprimeSourceIndex (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :=
  {P : Pset // IsCoprime K P.val} × (nset × bset)

instance (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :
    Fintype (CoprimeSourceIndex K Pset nset bset) := inferInstanceAs
      (Fintype ({P : Pset // IsCoprime K P.val} × (nset × bset)))

theorem weightedPhysicalReflectedRow_eq_coprime_source
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ x : CoprimeSourceIndex K Pset nset bset,
        r K*aw x.1.val.val*w x.2.1.val x.2.2.val*
          actualMixedCoefficient F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc u m x.2.1.val x.2.2.val := by
  unfold weightedPhysicalReflectedRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr_set {P : Pset | IsCoprime K P.val}
  · intro P hP
    simp only [Set.mem_ofPred_eq] at hP
    simp only [dite_eq_left hP]
    rw [Finset.sum_coe_sort nset (fun n : Ideal Eis => ∑ b : bset,
      r K*aw P.val*w n b.val*actualMixedCoefficient F K hK (S P.val) jF (D P hP) s hc u m n b.val)]
    apply Finset.sum_congr rfl
    intro n hn
    exact (Finset.sum_coe_sort bset (fun b : Ideal Eis =>
      r K*aw P.val*w n b*actualMixedCoefficient F K hK (S P.val) jF (D P hP) s hc u m n b)).symm
  · intro P hP
    simp only [Set.mem_ofPred_eq] at hP
    simp only [dite_eq_right hP,mul_zero,Finset.sum_const_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI
