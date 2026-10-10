import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries PrimeDyadicCover TemplateOneSidedPrior
open Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem original_block_eq_compiled {A : ℕ} {σ τ : Type} [Fintype σ] [Fintype τ]
    (Q H : ℕ) (Elong Eshort : Finset (PrimeUpTo A)) (hEshort : 0 < primeShellMass Eshort)
    (i : Index H) (ρ : 𝓢(ℝ,ℂ))
    (χ : ∀j:↥Eshort,MulChar (ZMod j.val.val) ℂ)
    (U : PrimeUpTo A → ℂ) (V : ↥Eshort → ℂ)
    (F : PrimeUpTo A → ↥Eshort → ℂ)
    (data : Fin Q → ↥Eshort → HistoryPolynomialData σ τ)
    (hdata : ∀p∈Elong,p.val∈block Q H (sourceNaturals Elong) i →
      ∀r:Fin Q,∀n:ℕ,Q*n+r.val=p.val → ∀j:↥Eshort,
        (data r j).weight ρ ((Q*n+r.val:ℕ):ℝ)=F p j) :
    oneSidedMean (sourceRowMass Q H Elong i) (sourceShortMass Eshort hEshort)
      (fun x=>sourceTest U (rowValue Q (2*lower Q H i+1) x)) V
      (rowCharacterKernel (fun j:↥Eshort=>j.val.val) χ Q (2*lower Q H i+1)
        (fun r:Fin Q=>r.val) (sourceRowAmplitude Q F)) =
    oneSidedMean (sourceRowMass Q H Elong i) (sourceShortMass Eshort hEshort)
      (fun x=>sourceTest (boundedSourceUnary Elong U) (rowValue Q (2*lower Q H i+1) x)) V
      (rowCharacterKernel (fun j:↥Eshort=>j.val.val) χ Q (2*lower Q H i+1)
        (fun r:Fin Q=>r.val) (fun r n j=>(data r j).weight ρ ((Q*n+r.val:ℕ):ℝ))) := by
  rw [source_oneSidedMean_eq_boundedSourceUnary]
  apply source_oneSidedMean_eq_extension
  intro x hx j
  obtain ⟨p,hp,he⟩ := sourceRowMass_ne_zero_exists_source Q H Elong i x hx
  have hm : p.val∈block Q H (sourceNaturals Elong) i := by
    rw [he]
    by_contra hh
    exact hx (by simp only [sourceRowMass,rowMass,ite_eq_right hh])
  have he' : Q*x.2.val+x.1.val=p.val := he.symm
  rw [sourceRowAmplitude,he',sourceTest_val]
  simpa only [he'] using (hdata p hp hm x.1 x.2 he' j).symm

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
