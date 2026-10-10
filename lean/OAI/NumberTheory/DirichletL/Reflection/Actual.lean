import OAI.NumberTheory.DirichletL.Reflection.Projections

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualMixedCoefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  s.amplitude u m n b *
    (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
      (s.modelDualNumerator u m n b)) *
    ∏ i, mixedActiveBracket (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) D i (s.modelDualNumerator u m n b)

theorem actualMixedCoefficient_factor (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*actualSlotPhase F S jF s u m*
        sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
          (F.reflected K hK S).generator_good (reflectedExponent jF)
          (frozenIndices φ (PrimeIndex K) σ) u m)*
      sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
        (frozenIndices φ (PrimeIndex K) σ) u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
      quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
      (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
      (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  obtain ⟨hRS,hF,hu⟩ := reflected_indices_partition φ (PrimeIndex K) σ
  have hF' : Disjoint (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ)
      (frozenIndices φ (PrimeIndex K) σ) := by
    simpa only [Finset.disjoint_left,Finset.mem_union] using hF
  have hu' : (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ) ∪
      frozenIndices φ (PrimeIndex K) σ = Finset.univ := by
    simpa only [Finset.ext_iff,Finset.mem_union] using hu
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.reflected K hK S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hr : Admissible (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) := by
    rw [F.reflected_residual_product K hK S]
    exact hK
  have he := mixed_coefficient_hybrid_original_exponents D s
    (F.reflected K hK S).generator_ne_zero hc (F.reflected K hK S).generator_good hcp
    (F.reflected K hK S).generator_primary _ _ _ hRS hF' hu'
    (reflectedExponent jF) (reflected_residual_exponent jF) hr u m n b hb
  have hcard : (slotIndices φ (PrimeIndex K) σ).card = Fintype.card σ := by
    rw [slotIndices,Finset.card_image_of_injective _ (Sum.inr_injective.comp Sum.inr_injective)]
    rfl
  rw [hcard,sourceRowPhase_eq_actual,sourceSlotPhase_eq_actual,
    F.reflected_residual_product K hK S,F.reflected_slot_product K hK S] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI
