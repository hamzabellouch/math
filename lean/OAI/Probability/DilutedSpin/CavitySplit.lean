import OAI.Probability.DilutedSpin.FinitePoissonSplit

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def oneNewRate (α : ℝ≥0) (q N : ℕ) : ℝ≥0 :=
  α*(q+1)*((N:ℝ≥0)/(N+1))^q

lemma cavityOldRate_card (α : ℝ≥0) (q N : ℕ) :
    (α*(N+1))*Fintype.card (Fin (q+1) → Fin N)/Fintype.card (Fin (q+1) → Fin (N+1)) =
      reservoirRate α q N := by
  simp only [Fintype.card_fun,Fintype.card_fin,
    reservoirRate,div_pow,pow_succ]
  have hn : (N:ℝ≥0)+1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma cavityOneRate_card (α : ℝ≥0) (q N : ℕ) :
    (α*(N+1))*Fintype.card (Fin (q+1) × (Fin q → Fin N))/Fintype.card (Fin (q+1) → Fin (N+1)) =
      oneNewRate α q N := by
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one,oneNewRate,div_pow,pow_succ]
  have hn : (N:ℝ≥0)+1 ≠ 0 := by positivity
  field_simp

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

open Classical in
/-- Exact old-site / one-new-site split of the physical Poisson energy after
 discarding only indices meeting the new site at least twice. No symmetry of
 the interaction has yet been used; the distinguished coordinate is explicit. -/
lemma cavity_compound_split (α : ℝ≥0) (q N : ℕ) [NeZero N]
    (V : X × (Fin (q+1) → Fin (N+1)) → E) (hV : Measurable V) :
    compoundPoisson (α*(N+1)) (Measure.map (fun z => if CavityGood z.2 then V z else 0)
      (μ.prod (finiteUniform (Fin (q+1) → Fin (N+1))))) =
      compoundPoisson (reservoirRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) → Fin N) => V (z.1,fun i => (z.2 i).succ))
          (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson (oneNewRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            V (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
          (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N))))) := by
  simpa only [cavityOldRate_card,cavityOneRate_card] using
    finite_poisson_split μ (fun x : Fin (q+1) → Fin N => fun i => (x i).succ)
      (fun z : Fin (q+1) × (Fin q → Fin N) => z.1.insertNth 0 (fun i => (z.2 i).succ))
      CavityGood (fun f => sum_cavityKeep f) V hV (α*(N+1))

end DilutedSpinGlass

end

end OAI
